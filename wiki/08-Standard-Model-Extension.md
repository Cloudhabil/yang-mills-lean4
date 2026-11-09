# Chapter 08: Full Standard Model Extension (70 Quanta)

In [`StandardModelExtension.lean`](../StandardModelExtension.lean) (`755 lines`), the pure 4D Yang–Mills formalization is extended to the complete physical **Standard Model of Particle Physics**:
$$\mathrm{SU}(3)_C \times \mathrm{SU}(2)_L \times \mathrm{U}(1)_Y$$

---

## 1. Physical Sectors and 70 Individual Quanta

The unified framework tracks all **70 individual Standard Model quanta**:

1. **61 Elementary Field Quanta**:
   * **12 Gauge Bosons**: 8 Gluons $g^{1\dots 8}$, 3 Electroweak $W^\pm, Z^0$, 1 Photon $\gamma$,
   * **1 Higgs Boson**: Neutral scalar $H^0$,
   * **12 Leptons**: 3 generations $\times$ (left-handed charged lepton $e_L, \mu_L, \tau_L$, right-handed $e_R, \mu_R, \tau_R$, left-handed neutrino $\nu_e, \nu_\mu, \nu_\tau$, and right-handed neutrino states),
   * **36 Quarks**: 6 flavours ($u, d, s, c, b, t$) $\times$ 3 colours ($r, g, b$) $\times$ 2 chiralities ($L, R$).

2. **9 Composite QCD Hadrons & Pure-Glue States**:
   * **3 Pseudoscalar Mesons**: $\pi^\pm, \pi^0$ (Goldstone GMOR pions),
   * **2 Strange Mesons**: $K^\pm$ (kaons),
   * **1 Vector Meson**: $\rho$ meson,
   * **2 Colour-Singlet Baryons**: Proton $p$ ($uud$), Neutron $n$ ($udd$),
   * **1 Baryon Resonance**: $\Delta^{++}$ ($uuu$),
   * **3 Glueballs & Odderons**: Scalar glueball $G(0^{++})$, tensor glueball $G(2^{++})$, and Odderon $O(3^{--})$.

---

## 2. Machine-Checked Anomaly Cancellation ($N_c = 3$)

In [`StandardModelExtension.lean`](../StandardModelExtension.lean):
```lean
theorem standard_model_anomaly_cancellation_unique_nc (Nc : ℕ) (h_anom : FullSMAnomalyFree Nc) :
    Nc = 3
```
This proves that the observed colour multiplicity $N_c = 3$ is not a free parameter, but the unique integer required for mathematical consistency.

---

## 3. Electroweak Weinberg Mixing & Massless Photon

The electroweak symmetry breaking mechanism is proven to preserve an exact zero eigenvalue:
```lean
theorem photon_strictly_massless (g g_prime v_higgs : ℝ) :
    (ElectroweakMassMatrix g g_prime v_higgs).det = 0
```
yielding $m_\gamma = 0$ while generating $M_W = \frac{1}{2} g v$ and $M_Z = \frac{1}{2} \sqrt{g^2 + g'^2} v$.
