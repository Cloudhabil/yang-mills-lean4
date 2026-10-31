"""High-Performance Vectorized PyTorch/CUDA 4D SU(3) Lattice Gauge Theory Engine.

Implements pure-GPU Cabibbo-Marinari SU(2) subgroup heatbath sweeps
for 4D SU(3) Yang-Mills gauge theory on NVIDIA GPU (RTX 4070 SUPER), computing:
1. Average plaquette action <P> = (1/3) Re Tr(P).
2. APE-smeared 0++ scalar glueball correlators C(t).
3. Planar Wilson loops W(R, T) and static potential V(R).
"""

from __future__ import annotations
import math
import numpy as np
import torch


def su3_reunitarize(U: torch.Tensor) -> torch.Tensor:
    """Gram-Schmidt orthonormalization for batched 3x3 complex matrices to guarantee U in SU(3)."""
    v0 = U[..., 0, :]
    u0 = v0 / torch.norm(v0, dim=-1, keepdim=True).clamp(min=1e-12)

    v1 = U[..., 1, :] - torch.sum(torch.conj(u0) * U[..., 1, :], dim=-1, keepdim=True) * u0
    u1 = v1 / torch.norm(v1, dim=-1, keepdim=True).clamp(min=1e-12)

    # u2 = (u0 x u1)* to ensure det(U) = 1
    u2_0 = torch.conj(u0[..., 1] * u1[..., 2] - u0[..., 2] * u1[..., 1])
    u2_1 = torch.conj(u0[..., 2] * u1[..., 0] - u0[..., 0] * u1[..., 2])
    u2_2 = torch.conj(u0[..., 0] * u1[..., 1] - u0[..., 1] * u1[..., 0])
    u2 = torch.stack([u2_0, u2_1, u2_2], dim=-1)

    return torch.stack([u0, u1, u2], dim=-2)


class SU3LatticeEngine:
    """4D SU(3) Lattice Engine running on CUDA."""

    def __init__(self, T: int, L: int, beta: float, device: str = "cuda"):
        self.T = T
        self.L = L
        self.beta = beta
        self.device = torch.device(device if torch.cuda.is_available() else "cpu")

        # Links shape: (4 directions, T, L, L, L, 3, 3) complex64
        self.shape = (4, T, L, L, L, 3, 3)
        self.links = torch.zeros(self.shape, dtype=torch.complex64, device=self.device)
        eye = torch.eye(3, dtype=torch.complex64, device=self.device)
        self.links[:] = eye

        # 4D Checkerboard parity mask
        t = torch.arange(T, device=self.device).view(T, 1, 1, 1)
        x = torch.arange(L, device=self.device).view(1, L, 1, 1)
        y = torch.arange(L, device=self.device).view(1, 1, L, 1)
        z = torch.arange(L, device=self.device).view(1, 1, 1, L)
        coord_sum = (t + x + y + z) % 2
        self.even_mask = (coord_sum == 0)
        self.odd_mask = (coord_sum == 1)

    def cold_start(self):
        eye = torch.eye(3, dtype=torch.complex64, device=self.device)
        self.links[:] = eye

    def compute_staples(self, mu: int) -> torch.Tensor:
        """Compute the sum of 6 staples surrounding links in direction mu."""
        staples = torch.zeros((self.T, self.L, self.L, self.L, 3, 3), dtype=torch.complex64, device=self.device)

        for nu in range(4):
            if nu == mu:
                continue

            u_nu_x = self.links[nu]
            u_mu_x_nu = torch.roll(self.links[mu], shifts=-1, dims=nu)
            u_nu_x_mu_dag = torch.roll(self.links[nu], shifts=-1, dims=mu).mH

            fwd = torch.matmul(torch.matmul(u_nu_x, u_mu_x_nu), u_nu_x_mu_dag)

            u_nu_xm_nu_dag = torch.roll(self.links[nu], shifts=1, dims=nu).mH
            u_mu_xm_nu = torch.roll(self.links[mu], shifts=1, dims=nu)
            u_nu_xm_nu_p_mu = torch.roll(torch.roll(self.links[nu], shifts=1, dims=nu), shifts=-1, dims=mu)

            bwd = torch.matmul(torch.matmul(u_nu_xm_nu_dag, u_mu_xm_nu), u_nu_xm_nu_p_mu)

            staples = staples + fwd + bwd

        return staples

    def cabibbo_marinari_update_subgroup(self, mu: int, mask: torch.Tensor, i1: int, i2: int):
        """Pure-GPU update of the 2x2 SU(2) subgroup (i1, i2) without host sync."""
        staples = self.compute_staples(mu)
        # V = U * Sigma^dagger
        V = torch.matmul(self.links[mu], staples.mH)

        a00 = V[..., i1, i1]
        a01 = V[..., i1, i2]
        a10 = V[..., i2, i1]
        a11 = V[..., i2, i2]

        s0 = (a00.real + a11.real) * 0.5
        s3 = (a00.imag - a11.imag) * 0.5
        s1 = (a01.imag + a10.imag) * 0.5
        s2 = (a01.real - a10.real) * 0.5

        k = torch.sqrt(s0**2 + s1**2 + s2**2 + s3**2 + 1e-12)
        v0 = s0 / k
        v1 = s1 / k
        v2 = s2 / k
        v3 = s3 / k

        alpha = (2.0 / 3.0) * self.beta * k

        # Pure-GPU Kennedy-Pendleton vectorization
        r1 = torch.rand_like(alpha).clamp(min=1e-8)
        r2 = torch.rand_like(alpha).clamp(min=1e-8)
        r3 = torch.rand_like(alpha)
        r4 = torch.rand_like(alpha)

        delta = -(torch.log(r1) + torch.log(r2) * (torch.cos(2.0 * math.pi * r3) ** 2)) / (alpha + 1e-8)
        cand_w0 = 1.0 - delta
        accept = (r4 ** 2 <= (1.0 - cand_w0 ** 2)) & (cand_w0 >= -1.0) & (cand_w0 <= 1.0)

        w0 = torch.where(accept, cand_w0, torch.zeros_like(cand_w0))
        still_needed = ~accept

        for _ in range(3):
            r1 = torch.rand_like(alpha).clamp(min=1e-8)
            r2 = torch.rand_like(alpha).clamp(min=1e-8)
            r3 = torch.rand_like(alpha)
            r4 = torch.rand_like(alpha)
            delta = -(torch.log(r1) + torch.log(r2) * (torch.cos(2.0 * math.pi * r3) ** 2)) / (alpha + 1e-8)
            cand = 1.0 - delta
            acc = (r4 ** 2 <= (1.0 - cand ** 2)) & (cand >= -1.0) & (cand <= 1.0) & still_needed
            w0 = torch.where(acc, cand, w0)
            still_needed = still_needed & ~acc

        fallback = (1.0 - 1.0 / (alpha + 1.0)).clamp(-1.0, 1.0)
        w0 = torch.where(still_needed, fallback, w0)

        phi = 2.0 * math.pi * torch.rand_like(alpha)
        cos_theta = 2.0 * torch.rand_like(alpha) - 1.0
        sin_theta = torch.sqrt((1.0 - cos_theta ** 2).clamp(min=0.0))

        sin_w = torch.sqrt((1.0 - w0 ** 2).clamp(min=0.0))
        w1 = sin_w * sin_theta * torch.cos(phi)
        w2 = sin_w * sin_theta * torch.sin(phi)
        w3 = sin_w * cos_theta

        # u = W * V
        u0 = w0*v0 - w1*v1 - w2*v2 - w3*v3
        u1 = w0*v1 + w1*v0 + w2*v3 - w3*v2
        u2 = w0*v2 - w1*v3 + w2*v0 + w3*v1
        u3 = w0*v3 + w1*v2 - w2*v1 + w3*v0

        m00 = torch.complex(u0, u3)
        m01 = torch.complex(u2, u1)
        m10 = torch.complex(-u2, u1)
        m11 = torch.complex(u0, -u3)

        u_i1 = self.links[mu, ..., i1, :].clone()
        u_i2 = self.links[mu, ..., i2, :].clone()

        new_i1 = m00.unsqueeze(-1) * u_i1 + m01.unsqueeze(-1) * u_i2
        new_i2 = m10.unsqueeze(-1) * u_i1 + m11.unsqueeze(-1) * u_i2

        mask_exp = mask.unsqueeze(-1)
        self.links[mu, ..., i1, :] = torch.where(mask_exp, new_i1, u_i1)
        self.links[mu, ..., i2, :] = torch.where(mask_exp, new_i2, u_i2)

    def sweep(self):
        """Execute 1 full Cabibbo-Marinari SU(3) heatbath sweep across all 3 subgroups."""
        subgroups = [(0, 1), (0, 2), (1, 2)]
        for mu in range(4):
            for i1, i2 in subgroups:
                self.cabibbo_marinari_update_subgroup(mu, self.even_mask, i1, i2)
                self.cabibbo_marinari_update_subgroup(mu, self.odd_mask, i1, i2)

        self.links = su3_reunitarize(self.links)

    def average_plaquette(self) -> float:
        """Calculate the average SU(3) plaquette: (1/3) Re Tr(P)."""
        plaq_sum = 0.0
        count = 0
        for mu in range(4):
            for nu in range(mu + 1, 4):
                u_mu_x = self.links[mu]
                u_nu_x_mu = torch.roll(self.links[nu], shifts=-1, dims=mu)
                u_mu_x_nu_dag = torch.roll(self.links[mu], shifts=-1, dims=nu).mH
                u_nu_x_dag = self.links[nu].mH

                p = torch.matmul(torch.matmul(torch.matmul(u_mu_x, u_nu_x_mu), u_mu_x_nu_dag), u_nu_x_dag)
                tr_p = (p[..., 0, 0] + p[..., 1, 1] + p[..., 2, 2]).real / 3.0
                plaq_sum += tr_p.sum().item()
                count += tr_p.numel()
        return plaq_sum / count

    def ape_smear_spatial(self, alpha_smear: float = 0.5, n_smear: int = 4) -> torch.Tensor:
        """Compute APE-smeared spatial links for SU(3)."""
        spatial_links = self.links[1:4].clone()

        for _ in range(n_smear):
            new_spatial = torch.zeros_like(spatial_links)
            for i, mu in enumerate([1, 2, 3]):
                staple_spatial = torch.zeros_like(spatial_links[i])
                for j, nu in enumerate([1, 2, 3]):
                    if nu == mu:
                        continue
                    u_nu_x = spatial_links[j]
                    u_mu_x_nu = torch.roll(spatial_links[i], shifts=-1, dims=nu)
                    u_nu_x_mu_dag = torch.roll(spatial_links[j], shifts=-1, dims=mu).mH
                    fwd = torch.matmul(torch.matmul(u_nu_x, u_mu_x_nu), u_nu_x_mu_dag)

                    u_nu_xm_nu_dag = torch.roll(spatial_links[j], shifts=1, dims=nu).mH
                    u_mu_xm_nu = torch.roll(spatial_links[i], shifts=1, dims=nu)
                    u_nu_xm_nu_p_mu = torch.roll(torch.roll(spatial_links[j], shifts=1, dims=nu), shifts=-1, dims=mu)
                    bwd = torch.matmul(torch.matmul(u_nu_xm_nu_dag, u_mu_xm_nu), u_nu_xm_nu_p_mu)

                    staple_spatial = staple_spatial + fwd + bwd

                comb = (1.0 - alpha_smear) * spatial_links[i] + (alpha_smear / 4.0) * staple_spatial
                new_spatial[i] = su3_reunitarize(comb)
            spatial_links = new_spatial

        return spatial_links

    def measure_glueball_operator(self, spatial_links: torch.Tensor) -> torch.Tensor:
        """Measure zero-momentum 0++ glueball operator O(t) for SU(3)."""
        O_t = torch.zeros(self.T, dtype=torch.float32, device=self.device)
        pairs = [(0, 1, 1, 2), (0, 2, 1, 3), (1, 2, 2, 3)]
        for i_idx, j_idx, mu, nu in pairs:
            u_i = spatial_links[i_idx]
            u_j_x_mu = torch.roll(spatial_links[j_idx], shifts=-1, dims=mu)
            u_i_x_nu_dag = torch.roll(spatial_links[i_idx], shifts=-1, dims=nu).mH
            u_j_dag = spatial_links[j_idx].mH

            p = torch.matmul(torch.matmul(torch.matmul(u_i, u_j_x_mu), u_i_x_nu_dag), u_j_dag)
            tr_p = (p[..., 0, 0] + p[..., 1, 1] + p[..., 2, 2]).real / 3.0
            p_slice = tr_p.sum(dim=(1, 2, 3))
            O_t = O_t + p_slice

        return O_t

    def measure_wilson_loops(self, max_R: int = 5, max_T: int = 5) -> np.ndarray:
        """Measure planar SU(3) Wilson loops W(R, T)."""
        W = np.zeros((max_R + 1, max_T + 1), dtype=np.float64)

        for r in range(1, max_R + 1):
            for t_len in range(1, max_T + 1):
                w_rt_sum = 0.0
                count = 0
                for spatial_dir in [1, 2, 3]:
                    U_line_R = self.links[spatial_dir].clone()
                    for step in range(1, r):
                        next_link = torch.roll(self.links[spatial_dir], shifts=-step, dims=spatial_dir)
                        U_line_R = torch.matmul(U_line_R, next_link)

                    U_line_T = self.links[0].clone()
                    for step in range(1, t_len):
                        next_link = torch.roll(self.links[0], shifts=-step, dims=0)
                        U_line_T = torch.matmul(U_line_T, next_link)

                    line_T_x_p_R = torch.roll(U_line_T, shifts=-r, dims=spatial_dir)
                    line_R_x_p_T_dag = torch.roll(U_line_R, shifts=-t_len, dims=0).mH
                    line_T_dag = U_line_T.mH

                    loop = torch.matmul(torch.matmul(torch.matmul(U_line_R, line_T_x_p_R), line_R_x_p_T_dag), line_T_dag)
                    tr_loop = (loop[..., 0, 0] + loop[..., 1, 1] + loop[..., 2, 2]).real / 3.0
                    w_rt_sum += tr_loop.mean().item()
                    count += 1

                W[r, t_len] = w_rt_sum / count

        return W
