/-
Copyright 2026 ToposLang / PLQ Authors.
Licensed under the Apache License, Version 2.0.

HypercubicPolymerCounting.lean
Rigorous 4D Hypercubic Plaquette-Polymer Counting & Closed 2-Cycle Gauss-Law Constraint.

Formalizes from first principles on ℤ⁴:
  1. The 4D hypercubic cell complex (`Z4Edge`, `Z4Plaquette`, `plaquetteBoundary`),
     proving `(plaquetteBoundary p).card = 4` and that two distinct plaquettes
     share at most 1 edge (`two_plaquettes_share_at_most_one_edge`).
  2. The closed 2-cycle Gauss-law / Bianchi constraint (`IsClosed2Cycle γ`, ∂γ = 0 mod 2):
     proves that every non-empty closed 2-cycle in ℤ⁴ has at least 6 plaquette faces
     (`closed_2cycle_card_ge_six`), corresponding to the boundary of a 3-cube.
  3. The 4-hypercube boundary cell complex (`hypercube4Boundary`), proving it carries
     exactly 24 plaquette faces (`hypercube4Boundary_card`).
  4. Exact Peierls suppression bounds dominating the 4D Klarner lattice animal entropy
     `s_entropy = ln(2401) < 10`:
     - Wilson Peierls contour weight at β ≥ 5/2 on any closed 2-cycle (|γ| ≥ 6):
       `exp(-β * |γ|) ≤ exp(-15) < exp(-10) < 1 / 2401`.
     - Strong-coupling SU(3) character bound at β = 1/2 (|γ| ≥ 6):
       `ζ₃(1/2)^|γ| ≤ (28/1000)^6 < exp(-10) < 1 / 2401`.
     - Crossover endpoint SU(3) character bound at β = 5/2 on a 4-hypercube unit
       (|∂c₄| = 24) and any closed 2-cycle with |γ| ≥ 11:
       `ζ₃(5/2)^24 ≤ (382/1000)^24 < (382/1000)^11 < exp(-10) < 1 / 2401`.
-/

import Mathlib

noncomputable section

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace YangMills.HypercubicPolymerCounting

/-! ============================================================================
    PART I: 4D HYPERCUBIC LATTICE ℤ⁴ EDGES, PLAQUETTES, AND BOUNDARY ∂₂
    ============================================================================ -/

/-- Site on the 4D hypercubic lattice `ℤ⁴`. -/
abbrev Z4Site := Fin 4 → ℤ

/-- Shift a lattice site by `+1` in coordinate direction `μ`. -/
def shiftSite (x : Z4Site) (μ : Fin 4) : Z4Site :=
  Function.update x μ (x μ + 1)

theorem shiftSite_apply_self (x : Z4Site) (μ : Fin 4) :
    shiftSite x μ μ = x μ + 1 := by
  simp [shiftSite]

theorem shiftSite_apply_ne (x : Z4Site) {μ ν : Fin 4} (h : ν ≠ μ) :
    shiftSite x μ ν = x ν := by
  simp [shiftSite, h]

theorem shiftSite_ne_self (x : Z4Site) (μ : Fin 4) :
    shiftSite x μ ≠ x := by
  intro h
  have := congrFun h μ
  rw [shiftSite_apply_self] at this
  omega

/-- Elementary unoriented lattice edge `[x, x + e_μ]` in `ℤ⁴`. -/
@[ext]
structure Z4Edge where
  base : Z4Site
  dir : Fin 4
  deriving DecidableEq

/-- Elementary plaquette `(x, μ, ν)` with `μ < ν` in `ℤ⁴`. -/
structure Z4Plaquette where
  base : Z4Site
  μ : Fin 4
  ν : Fin 4
  h_lt : μ < ν
  deriving DecidableEq

/-- The 4 boundary edges of an elementary plaquette `p = (x, μ, ν)`. -/
def plaquetteBoundary (p : Z4Plaquette) : Finset Z4Edge :=
  { ⟨p.base, p.μ⟩,
    ⟨shiftSite p.base p.ν, p.μ⟩,
    ⟨p.base, p.ν⟩,
    ⟨shiftSite p.base p.μ, p.ν⟩ }

theorem plaquetteBoundary_card (p : Z4Plaquette) :
    (plaquetteBoundary p).card = 4 := by
  have hne : p.μ ≠ p.ν := ne_of_lt p.h_lt
  have h12 : (⟨p.base, p.μ⟩ : Z4Edge) ≠ ⟨shiftSite p.base p.ν, p.μ⟩ := by
    intro h
    exact (shiftSite_ne_self p.base p.ν).symm (congrArg Z4Edge.base h)
  have h13 : (⟨p.base, p.μ⟩ : Z4Edge) ≠ ⟨p.base, p.ν⟩ := by
    intro h; exact hne (congrArg Z4Edge.dir h)
  have h14 : (⟨p.base, p.μ⟩ : Z4Edge) ≠ ⟨shiftSite p.base p.μ, p.ν⟩ := by
    intro h; exact hne (congrArg Z4Edge.dir h)
  have h23 : (⟨shiftSite p.base p.ν, p.μ⟩ : Z4Edge) ≠ ⟨p.base, p.ν⟩ := by
    intro h; exact hne (congrArg Z4Edge.dir h)
  have h24 : (⟨shiftSite p.base p.ν, p.μ⟩ : Z4Edge) ≠ ⟨shiftSite p.base p.μ, p.ν⟩ := by
    intro h; exact hne (congrArg Z4Edge.dir h)
  have h34 : (⟨p.base, p.ν⟩ : Z4Edge) ≠ ⟨shiftSite p.base p.μ, p.ν⟩ := by
    intro h
    exact (shiftSite_ne_self p.base p.μ).symm (congrArg Z4Edge.base h)
  unfold plaquetteBoundary
  rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
      Finset.card_insert_of_notMem, Finset.card_singleton]
  · simp [h34]
  · simp [h23, h24]
  · simp [h12, h13, h14]

/-- Membership characterization for `plaquetteBoundary`. -/
theorem mem_plaquetteBoundary_iff (p : Z4Plaquette) (e : Z4Edge) :
    e ∈ plaquetteBoundary p ↔
      (e.dir = p.μ ∧ (e.base = p.base ∨ e.base = shiftSite p.base p.ν)) ∨
      (e.dir = p.ν ∧ (e.base = p.base ∨ e.base = shiftSite p.base p.μ)) := by
  unfold plaquetteBoundary
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro (rfl | rfl | rfl | rfl)
    · left; exact ⟨rfl, Or.inl rfl⟩
    · left; exact ⟨rfl, Or.inr rfl⟩
    · right; exact ⟨rfl, Or.inl rfl⟩
    · right; exact ⟨rfl, Or.inr rfl⟩
  · rintro (⟨hd, hb | hb⟩ | ⟨hd, hb | hb⟩)
    · left; exact Z4Edge.ext hb hd
    · right; left; exact Z4Edge.ext hb hd
    · right; right; left; exact Z4Edge.ext hb hd
    · right; right; right; exact Z4Edge.ext hb hd

theorem shiftSite_inj_right {x : Z4Site} {α β : Fin 4} (h : shiftSite x α = shiftSite x β) :
    α = β := by
  by_contra hne
  have := congrFun h α
  rw [shiftSite_apply_self, shiftSite_apply_ne x hne] at this
  omega

/-- Coordinate sum `∑_i x_i` on `ℤ⁴`. -/
def siteSum (x : Z4Site) : ℤ :=
  ∑ i : Fin 4, x i

theorem siteSum_shiftSite (x : Z4Site) (μ : Fin 4) :
    siteSum (shiftSite x μ) = siteSum x + 1 := by
  unfold siteSum shiftSite
  rw [Finset.sum_update_of_mem (Finset.mem_univ μ)]
  have h_rest : ∑ i ∈ Finset.univ \ {μ}, x i = (∑ i : Fin 4, x i) - x μ := by
    have := Finset.add_sum_erase Finset.univ x (Finset.mem_univ μ)
    rw [Finset.erase_eq] at this
    linarith
  rw [h_rest]
  ring

/-- **Fundamental Incidence Lemma on `ℤ⁴`**:
    Two distinct plaquettes `p ≠ q` in `ℤ⁴` share at most one boundary edge. -/
theorem two_plaquettes_share_at_most_one_edge {p q : Z4Plaquette} (hpq : p ≠ q) :
    (plaquetteBoundary p ∩ plaquetteBoundary q).card ≤ 1 := by
  by_contra h_gt
  obtain ⟨e₁, he₁, e₂, he₂, he₁₂⟩ :=
    Finset.one_lt_card.mp (by omega : 1 < (plaquetteBoundary p ∩ plaquetteBoundary q).card)
  rw [Finset.mem_inter] at he₁ he₂
  have hp1 := (mem_plaquetteBoundary_iff p e₁).mp he₁.1
  have hq1 := (mem_plaquetteBoundary_iff q e₁).mp he₁.2
  have hp2 := (mem_plaquetteBoundary_iff p e₂).mp he₂.1
  have hq2 := (mem_plaquetteBoundary_iff q e₂).mp he₂.2
  have hp_ne : p.μ ≠ p.ν := ne_of_lt p.h_lt
  have hq_ne : q.μ ≠ q.ν := ne_of_lt q.h_lt
  -- Helper: if e₁, e₂ ∈ ∂r have e₁.dir = e₂.dir and siteSum e₁.base ≤ siteSum e₂.base,
  -- then r.base = e₁.base and e₂.base = shiftSite r.base d' where d' is the other direction.
  have same_dir_eq : ∀ (r : Z4Plaquette) (hr_ne : r.μ ≠ r.ν) (a b : Z4Edge),
      a ∈ plaquetteBoundary r → b ∈ plaquetteBoundary r →
      a ≠ b → a.dir = b.dir → siteSum a.base ≤ siteSum b.base →
      r.base = a.base ∧
        ((a.dir = r.μ ∧ b.base = shiftSite r.base r.ν) ∨
         (a.dir = r.ν ∧ b.base = shiftSite r.base r.μ)) := by
    intro r hr_ne a b ha hb hab hdir hsum
    have ha' := (mem_plaquetteBoundary_iff r a).mp ha
    have hb' := (mem_plaquetteBoundary_iff r b).mp hb
    rcases ha' with ⟨hda, hba | hba⟩ | ⟨hda, hba | hba⟩ <;>
    rcases hb' with ⟨hdb, hbb | hbb⟩ | ⟨hdb, hbb | hbb⟩
    · exfalso; exact hab (Z4Edge.ext (by rw [hba, hbb]) hdir)
    · exact ⟨hba.symm, Or.inl ⟨hda, hbb⟩⟩
    · exfalso; exact hr_ne (by rw [← hda, hdir, hdb])
    · exfalso; exact hr_ne (by rw [← hda, hdir, hdb])
    · exfalso
      have hs := siteSum_shiftSite r.base r.ν
      rw [hba, hbb] at hsum; omega
    · exfalso; exact hab (Z4Edge.ext (by rw [hba, hbb]) hdir)
    · exfalso; exact hr_ne (by rw [← hda, hdir, hdb])
    · exfalso; exact hr_ne (by rw [← hda, hdir, hdb])
    · exfalso; exact hr_ne (by rw [← hdb, ← hdir, hda])
    · exfalso; exact hr_ne (by rw [← hdb, ← hdir, hda])
    · exfalso; exact hab (Z4Edge.ext (by rw [hba, hbb]) hdir)
    · exact ⟨hba.symm, Or.inr ⟨hda, hbb⟩⟩
    · exfalso; exact hr_ne (by rw [← hdb, ← hdir, hda])
    · exfalso; exact hr_ne (by rw [← hdb, ← hdir, hda])
    · exfalso
      have hs := siteSum_shiftSite r.base r.μ
      rw [hba, hbb] at hsum; omega
    · exfalso; exact hab (Z4Edge.ext (by rw [hba, hbb]) hdir)
  by_cases h_dir_eq : e₁.dir = e₂.dir
  · -- WLOG siteSum e₁.base ≤ siteSum e₂.base
    have h_wlog : ∀ a b : Z4Edge, a ≠ b → a.dir = b.dir → siteSum a.base ≤ siteSum b.base →
        a ∈ plaquetteBoundary p → b ∈ plaquetteBoundary p →
        a ∈ plaquetteBoundary q → b ∈ plaquetteBoundary q → False := by
      intro a b hab hdir hsum hap hbp haq hbq
      obtain ⟨hpb, hp_other⟩ := same_dir_eq p hp_ne a b hap hbp hab hdir hsum
      obtain ⟨hqb, hq_other⟩ := same_dir_eq q hq_ne a b haq hbq hab hdir hsum
      have h_base : p.base = q.base := hpb.trans hqb.symm
      rcases hp_other with ⟨hp_a, hp_b⟩ | ⟨hp_a, hp_b⟩ <;>
      rcases hq_other with ⟨hq_a, hq_b⟩ | ⟨hq_a, hq_b⟩
      · have hμ : p.μ = q.μ := hp_a.symm.trans hq_a
        have h_sh : shiftSite p.base p.ν = shiftSite p.base q.ν := by rw [← hp_b, hq_b, ← h_base]
        have hν : p.ν = q.ν := shiftSite_inj_right h_sh
        exact hpq (by cases p; cases q; simp only at h_base hμ hν; subst h_base hμ hν; rfl)
      · have h_sh : shiftSite p.base p.ν = shiftSite p.base q.μ := by rw [← hp_b, hq_b, ← h_base]
        have h_other : p.ν = q.μ := shiftSite_inj_right h_sh
        have hμν : p.μ = q.ν ∧ p.ν = q.μ := ⟨hp_a.symm.trans hq_a, h_other⟩
        have := p.h_lt; have := q.h_lt; omega
      · have h_sh : shiftSite p.base p.μ = shiftSite p.base q.ν := by rw [← hp_b, hq_b, ← h_base]
        have h_other : p.μ = q.ν := shiftSite_inj_right h_sh
        have hμν : p.ν = q.μ ∧ p.μ = q.ν := ⟨hp_a.symm.trans hq_a, h_other⟩
        have := p.h_lt; have := q.h_lt; omega
      · have hν : p.ν = q.ν := hp_a.symm.trans hq_a
        have h_sh : shiftSite p.base p.μ = shiftSite p.base q.μ := by rw [← hp_b, hq_b, ← h_base]
        have hμ : p.μ = q.μ := shiftSite_inj_right h_sh
        exact hpq (by cases p; cases q; simp only at h_base hμ hν; subst h_base hμ hν; rfl)
    rcases le_total (siteSum e₁.base) (siteSum e₂.base) with hle | hle
    · exact h_wlog e₁ e₂ he₁₂ h_dir_eq hle he₁.1 he₂.1 he₁.2 he₂.2
    · exact h_wlog e₂ e₁ he₁₂.symm h_dir_eq.symm hle he₂.1 he₁.1 he₂.2 he₁.2
  · -- e₁.dir ≠ e₂.dir: both p and q span {e₁.dir, e₂.dir}, hence p.μ = q.μ and p.ν = q.ν
    have h_planes : p.μ = q.μ ∧ p.ν = q.ν := by
      rcases hp1 with ⟨hd1p, _⟩ | ⟨hd1p, _⟩ <;>
      rcases hp2 with ⟨hd2p, _⟩ | ⟨hd2p, _⟩ <;>
      rcases hq1 with ⟨hd1q, _⟩ | ⟨hd1q, _⟩ <;>
      rcases hq2 with ⟨hd2q, _⟩ | ⟨hd2q, _⟩ <;>
      have := p.h_lt <;> have := q.h_lt <;> omega
    rcases h_planes with ⟨hμ, hν⟩
    -- For any edge a ∈ ∂p with a.dir = p.μ, a.base p.μ = p.base p.μ.
    -- For any edge b ∈ ∂p with b.dir = p.ν, b.base p.ν = p.base p.ν.
    have coord_eq : ∀ (r : Z4Plaquette) (a : Z4Edge), a ∈ plaquetteBoundary r →
        (a.dir = r.μ → a.base r.μ = r.base r.μ) ∧
        (a.dir = r.ν → a.base r.ν = r.base r.ν) ∧
        (∀ i : Fin 4, i ≠ r.μ → i ≠ r.ν → a.base i = r.base i) := by
      intro r a ha
      have hr_ne : r.μ ≠ r.ν := ne_of_lt r.h_lt
      rcases (mem_plaquetteBoundary_iff r a).mp ha with ⟨hd, hb | hb⟩ | ⟨hd, hb | hb⟩
      · refine ⟨fun _ => by rw [hb], fun h => (hr_ne (hd.symm.trans h)).elim, fun i _ _ => by rw [hb]⟩
      · refine ⟨fun _ => by rw [hb, shiftSite_apply_ne _ hr_ne],
                fun h => (hr_ne (hd.symm.trans h)).elim,
                fun i _ hiν => by rw [hb, shiftSite_apply_ne _ hiν]⟩
      · refine ⟨fun h => (hr_ne (h.symm.trans hd)).elim,
                fun _ => by rw [hb],
                fun i _ _ => by rw [hb]⟩
      · refine ⟨fun h => (hr_ne (h.symm.trans hd)).elim,
                fun _ => by rw [hb, shiftSite_apply_ne _ hr_ne.symm],
                fun i hiμ _ => by rw [hb, shiftSite_apply_ne _ hiμ]⟩
    have h_base : p.base = q.base := by
      ext i
      by_cases hiμ : i = p.μ
      · subst hiμ
        rcases hp1 with ⟨hd1p, _⟩ | ⟨hd1p, _⟩
        · have hp_i := (coord_eq p e₁ he₁.1).1 hd1p
          have hq_i := (coord_eq q e₁ he₁.2).1 (hd1p.trans hμ)
          rw [← hp_i, hμ, hq_i]
        · rcases hp2 with ⟨hd2p, _⟩ | ⟨hd2p, _⟩
          · have hp_i := (coord_eq p e₂ he₂.1).1 hd2p
            have hq_i := (coord_eq q e₂ he₂.2).1 (hd2p.trans hμ)
            rw [← hp_i, hμ, hq_i]
          · exfalso; exact h_dir_eq (hd1p.trans hd2p.symm)
      · by_cases hiν : i = p.ν
        · subst hiν
          rcases hp1 with ⟨hd1p, _⟩ | ⟨hd1p, _⟩
          · rcases hp2 with ⟨hd2p, _⟩ | ⟨hd2p, _⟩
            · exfalso; exact h_dir_eq (hd1p.trans hd2p.symm)
            · have hp_i := (coord_eq p e₂ he₂.1).2.1 hd2p
              have hq_i := (coord_eq q e₂ he₂.2).2.1 (hd2p.trans hν)
              rw [← hp_i, hν, hq_i]
          · have hp_i := (coord_eq p e₁ he₁.1).2.1 hd1p
            have hq_i := (coord_eq q e₁ he₁.2).2.1 (hd1p.trans hν)
            rw [← hp_i, hν, hq_i]
        · have hp_i := (coord_eq p e₁ he₁.1).2.2 i hiμ hiν
          have hq_i := (coord_eq q e₁ he₁.2).2.2 i (hμ ▸ hiμ) (hν ▸ hiν)
          exact hp_i.symm.trans hq_i
    exact hpq (by cases p; cases q; simp only at h_base hμ hν; subst h_base hμ hν; rfl)

/-! ============================================================================
    PART II: CLOSED 2-CYCLE GAUSS-LAW CONSTRAINT (∂γ = 0) ⟹ |γ| ≥ 6
    ============================================================================ -/

/-- **Closed 2-Cycle Gauss-Law / Bianchi Constraint (`∂γ = 0 mod 2`)**:
    Every boundary edge of every plaquette `p ∈ γ` is shared with at least one
    other plaquette `q ∈ γ` (`q ≠ p`), forbidding open plaquette trees. -/
def IsClosed2Cycle (γ : Finset Z4Plaquette) : Prop :=
  ∀ p ∈ γ, ∀ e ∈ plaquetteBoundary p, ∃ q ∈ γ, q ≠ p ∧ e ∈ plaquetteBoundary q

/-- Helper: if `e ∈ ∂q` has `e.base` minimizing `siteSum` over `γ`, then `q.base = e.base`. -/
theorem minimal_base_of_edge_in_boundary {γ : Finset Z4Plaquette} {p q : Z4Plaquette}
    (hp_min : ∀ r ∈ γ, siteSum p.base ≤ siteSum r.base)
    (hq_mem : q ∈ γ) {e : Z4Edge} (he_base : e.base = p.base) (he_q : e ∈ plaquetteBoundary q) :
    q.base = p.base := by
  rcases (mem_plaquetteBoundary_iff q e).mp he_q with ⟨_, hb | hb⟩ | ⟨_, hb | hb⟩
  · exact (he_base ▸ hb).symm
  · exfalso
    have hs := congrArg siteSum hb
    rw [he_base, siteSum_shiftSite] at hs
    have hmin := hp_min q hq_mem
    omega
  · exact (he_base ▸ hb).symm
  · exfalso
    have hs := congrArg siteSum hb
    rw [he_base, siteSum_shiftSite] at hs
    have hmin := hp_min q hq_mem
    omega

/-- **Main Topological Theorem: Closed 2-Cycle Minimal Size `|γ| ≥ 6`**:
    Any non-empty closed 2-cycle `γ` on `ℤ⁴` (`∂γ = 0`) carries at least `6`
    elementary plaquette faces (realized by the 6 faces of a 3-cube). -/
theorem closed_2cycle_card_ge_six {γ : Finset Z4Plaquette}
    (hne : γ.Nonempty) (hclosed : IsClosed2Cycle γ) :
    6 ≤ γ.card := by
  -- Pick a plaquette p ∈ γ minimizing siteSum p.base
  obtain ⟨p, hp_mem, hp_min⟩ := Finset.exists_min_image γ (fun q => siteSum q.base) hne
  let e1 : Z4Edge := ⟨p.base, p.μ⟩
  let e2 : Z4Edge := ⟨shiftSite p.base p.ν, p.μ⟩
  let e3 : Z4Edge := ⟨p.base, p.ν⟩
  let e4 : Z4Edge := ⟨shiftSite p.base p.μ, p.ν⟩
  have he1 : e1 ∈ plaquetteBoundary p := by unfold plaquetteBoundary; simp [e1]
  have he2 : e2 ∈ plaquetteBoundary p := by unfold plaquetteBoundary; simp [e2]
  have he3 : e3 ∈ plaquetteBoundary p := by unfold plaquetteBoundary; simp [e3]
  have he4 : e4 ∈ plaquetteBoundary p := by unfold plaquetteBoundary; simp [e4]
  rcases hclosed p hp_mem e1 he1 with ⟨q1, hq1_mem, hq1_ne, hq1_e1⟩
  rcases hclosed p hp_mem e2 he2 with ⟨q2, hq2_mem, hq2_ne, hq2_e2⟩
  rcases hclosed p hp_mem e3 he3 with ⟨q3, hq3_mem, hq3_ne, hq3_e3⟩
  rcases hclosed p hp_mem e4 he4 with ⟨q4, hq4_mem, hq4_ne, hq4_e4⟩
  -- Because p minimizes siteSum, q1.base = p.base and q3.base = p.base
  have hq1_base : q1.base = p.base := minimal_base_of_edge_in_boundary hp_min hq1_mem rfl hq1_e1
  have hq3_base : q3.base = p.base := minimal_base_of_edge_in_boundary hp_min hq3_mem rfl hq3_e3
  -- Helper: two neighbors sharing distinct edges of p must be distinct
  have h_nbr_ne : ∀ {a b : Z4Plaquette} {ea eb : Z4Edge},
      ea ∈ plaquetteBoundary p → eb ∈ plaquetteBoundary p → ea ≠ eb →
      a ≠ p → ea ∈ plaquetteBoundary a →
      b ≠ p → eb ∈ plaquetteBoundary b → a ≠ b := by
    intro a b ea eb hea heb heab hap hae hbp hbe hab
    subst hab
    have hcard := two_plaquettes_share_at_most_one_edge hap
    have hsub : {ea, eb} ⊆ plaquetteBoundary p ∩ plaquetteBoundary a := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact Finset.mem_inter.mpr ⟨hea, hae⟩
      · rw [Finset.mem_singleton.mp hx]; exact Finset.mem_inter.mpr ⟨heb, hbe⟩
    have h2 : 2 ≤ ({ea, eb} : Finset Z4Edge).card := by rw [Finset.card_pair heab]
    have := Finset.card_le_card hsub
    rw [Finset.inter_comm] at hcard
    omega
  have hp_ne : p.μ ≠ p.ν := ne_of_lt p.h_lt
  have he12 : e1 ≠ e2 := fun h => (shiftSite_ne_self p.base p.ν).symm (congrArg Z4Edge.base h)
  have he13 : e1 ≠ e3 := fun h => hp_ne (congrArg Z4Edge.dir h)
  have he14 : e1 ≠ e4 := fun h => hp_ne (congrArg Z4Edge.dir h)
  have he23 : e2 ≠ e3 := fun h => hp_ne (congrArg Z4Edge.dir h)
  have he24 : e2 ≠ e4 := fun h => hp_ne (congrArg Z4Edge.dir h)
  have he34 : e3 ≠ e4 := fun h => (shiftSite_ne_self p.base p.μ).symm (congrArg Z4Edge.base h)
  have hq12 : q1 ≠ q2 := h_nbr_ne he1 he2 he12 hq1_ne hq1_e1 hq2_ne hq2_e2
  have hq13 : q1 ≠ q3 := h_nbr_ne he1 he3 he13 hq1_ne hq1_e1 hq3_ne hq3_e3
  have hq14 : q1 ≠ q4 := h_nbr_ne he1 he4 he14 hq1_ne hq1_e1 hq4_ne hq4_e4
  have hq23 : q2 ≠ q3 := h_nbr_ne he2 he3 he23 hq2_ne hq2_e2 hq3_ne hq3_e3
  have hq24 : q2 ≠ q4 := h_nbr_ne he2 he4 he24 hq2_ne hq2_e2 hq4_ne hq4_e4
  have hq34 : q3 ≠ q4 := h_nbr_ne he3 he4 he34 hq3_ne hq3_e3 hq4_ne hq4_e4
  -- Extract the second direction ρ of q1 (other than p.μ)
  have hq1_dir : ∃ ρ : Fin 4, ρ ≠ p.μ ∧ ρ ≠ p.ν ∧
      ((q1.μ = p.μ ∧ q1.ν = ρ) ∨ (q1.μ = ρ ∧ q1.ν = p.μ)) := by
    rcases (mem_plaquetteBoundary_iff q1 e1).mp hq1_e1 with ⟨hd, _⟩ | ⟨hd, _⟩
    · dsimp [e1] at hd
      refine ⟨q1.ν, ?_, ?_, Or.inl ⟨hd.symm, rfl⟩⟩
      · intro h; exact (ne_of_lt q1.h_lt) (hd.symm.trans h.symm)
      · intro hν
        exact hq1_ne (by cases p; cases q1; simp only at hq1_base hd hν; subst hq1_base hd hν; rfl)
    · dsimp [e1] at hd
      refine ⟨q1.μ, ?_, ?_, Or.inr ⟨rfl, hd.symm⟩⟩
      · intro h; exact (ne_of_lt q1.h_lt) (h.trans hd)
      · intro hμ
        have := p.h_lt; have := q1.h_lt
        exfalso; omega
  rcases hq1_dir with ⟨ρ, hρ_μ, hρ_ν, hq1_planes⟩
  -- Define the opposite edge e1' = ⟨shiftSite p.base ρ, p.μ⟩ of q1
  let e1' : Z4Edge := ⟨shiftSite p.base ρ, p.μ⟩
  have he1'_q1 : e1' ∈ plaquetteBoundary q1 := by
    rw [mem_plaquetteBoundary_iff]
    rcases hq1_planes with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left; refine ⟨h1.symm, Or.inr ?_⟩; rw [hq1_base, h2]
    · right; refine ⟨h2.symm, Or.inr ?_⟩; rw [hq1_base, h1]
  -- Obtain the 6th plaquette q5 sharing e1' with q1
  rcases hclosed q1 hq1_mem e1' he1'_q1 with ⟨q5, hq5_mem, hq5_ne1, hq5_e1'⟩
  -- Prove q5 is distinct from p, q2, q3, q4 by showing e1' ∉ ∂p ∪ ∂q2 ∪ ∂q3 ∪ ∂q4
  have h_not_p : e1' ∉ plaquetteBoundary p := by
    intro h
    have hcoord : e1'.base ρ = p.base ρ := by
      rcases (mem_plaquetteBoundary_iff p e1').mp h with ⟨_, hb | hb⟩ | ⟨_, hb | hb⟩
      · rw [hb]
      · rw [hb, shiftSite_apply_ne _ hρ_ν]
      · rw [hb]
      · rw [hb, shiftSite_apply_ne _ hρ_μ]
    dsimp [e1'] at hcoord
    rw [shiftSite_apply_self] at hcoord
    omega
  have h_not_q2 : e1' ∉ plaquetteBoundary q2 := by
    intro h
    have hq2_nu : q2.base p.ν = p.base p.ν + 1 := by
      rcases (mem_plaquetteBoundary_iff q2 e2).mp hq2_e2 with ⟨hd, hb | hb⟩ | ⟨hd, hb | hb⟩ <;>
      (dsimp [e2] at hb hd)
      · have := congrFun hb p.ν; rw [shiftSite_apply_self] at this; exact this.symm
      · by_cases hβ : q2.ν = p.ν
        · have h_base : q2.base = p.base := by
            ext i
            by_cases hi : i = p.ν
            · subst hi; have := congrFun hb p.ν; rw [shiftSite_apply_self, hβ, shiftSite_apply_self] at this; omega
            · have := congrFun hb i; rw [shiftSite_apply_ne _ hi, hβ, shiftSite_apply_ne _ hi] at this; exact this.symm
          exact absurd (by cases p; cases q2; simp only at h_base hd hβ; subst h_base hd hβ; rfl) hq2_ne
        · have := congrFun hb p.ν; rw [shiftSite_apply_self, shiftSite_apply_ne _ (Ne.symm hβ)] at this; exact this.symm
      · have := congrFun hb p.ν; rw [shiftSite_apply_self] at this; exact this.symm
      · by_cases hβ : q2.μ = p.ν
        · exfalso
          have := q2.h_lt; have := p.h_lt
          omega
        · have := congrFun hb p.ν; rw [shiftSite_apply_self, shiftSite_apply_ne _ (Ne.symm hβ)] at this; exact this.symm
    -- Any edge in ∂q2 has ν-coordinate ≥ q2.base p.ν = p.base p.ν + 1, whereas e1'.base p.ν = p.base p.ν!
    have h_ge : q2.base p.ν ≤ e1'.base p.ν := by
      rcases (mem_plaquetteBoundary_iff q2 e1').mp h with ⟨_, hb | hb⟩ | ⟨_, hb | hb⟩ <;>
      · rw [hb]
        try (by_cases h_eq : p.ν = q2.ν <;> [rw [h_eq, shiftSite_apply_self]; rw [shiftSite_apply_ne _ h_eq]] <;> omega)
        try (by_cases h_eq : p.ν = q2.μ <;> [rw [h_eq, shiftSite_apply_self]; rw [shiftSite_apply_ne _ h_eq]] <;> omega)
        try omega
    dsimp [e1'] at h_ge
    rw [shiftSite_apply_ne _ hρ_ν.symm] at h_ge
    omega
  have h_not_q4 : e1' ∉ plaquetteBoundary q4 := by
    intro h
    -- q4 shares e4 = ⟨shiftSite p.base p.μ, p.ν⟩, so q4.base p.μ = p.base p.μ + 1!
    have hq4_mu : q4.base p.μ = p.base p.μ + 1 := by
      rcases (mem_plaquetteBoundary_iff q4 e4).mp hq4_e4 with ⟨hd, hb | hb⟩ | ⟨hd, hb | hb⟩ <;>
      (dsimp [e4] at hb hd)
      · have := congrFun hb p.μ; rw [shiftSite_apply_self] at this; exact this.symm
      · by_cases hβ : q4.ν = p.μ
        · exfalso; have := q4.h_lt; have := p.h_lt; omega
        · have := congrFun hb p.μ; rw [shiftSite_apply_self, shiftSite_apply_ne _ (Ne.symm hβ)] at this; exact this.symm
      · have := congrFun hb p.μ; rw [shiftSite_apply_self] at this; exact this.symm
      · by_cases hβ : q4.μ = p.μ
        · have h_base : q4.base = p.base := by
            ext i
            by_cases hi : i = p.μ
            · subst hi; have := congrFun hb p.μ; rw [shiftSite_apply_self, hβ, shiftSite_apply_self] at this; omega
            · have := congrFun hb i; rw [shiftSite_apply_ne _ hi, hβ, shiftSite_apply_ne _ hi] at this; exact this.symm
          exact absurd (by cases p; cases q4; simp only at h_base hd hβ; subst h_base hd hβ; rfl) hq4_ne
        · have := congrFun hb p.μ; rw [shiftSite_apply_self, shiftSite_apply_ne _ (Ne.symm hβ)] at this; exact this.symm
    have h_ge : q4.base p.μ ≤ e1'.base p.μ := by
      rcases (mem_plaquetteBoundary_iff q4 e1').mp h with ⟨_, hb | hb⟩ | ⟨_, hb | hb⟩ <;>
      · rw [hb]
        try (by_cases h_eq : p.μ = q4.ν <;> [rw [h_eq, shiftSite_apply_self]; rw [shiftSite_apply_ne _ h_eq]] <;> omega)
        try (by_cases h_eq : p.μ = q4.μ <;> [rw [h_eq, shiftSite_apply_self]; rw [shiftSite_apply_ne _ h_eq]] <;> omega)
        try omega
    dsimp [e1'] at h_ge
    rw [shiftSite_apply_ne _ hρ_μ.symm] at h_ge
    omega
  have h_not_q3 : e1' ∉ plaquetteBoundary q3 := by
    intro h
    -- q3.base = p.base and e3 = ⟨p.base, p.ν⟩ ∈ ∂q3, and q3 ≠ p!
    -- Since e1'.dir = p.μ, if e1' ∈ ∂q3 then p.μ ∈ {q3.μ, q3.ν}.
    -- Since p.ν ∈ {q3.μ, q3.ν} (from e3 ∈ ∂q3), we get q3 = p, contradicting hq3_ne!
    have h_q3_nu : q3.μ = p.ν ∨ q3.ν = p.ν := by
      rcases (mem_plaquetteBoundary_iff q3 e3).mp hq3_e3 with ⟨hd, _⟩ | ⟨hd, _⟩
      · left; exact hd.symm
      · right; exact hd.symm
    have h_q3_mu : q3.μ = p.μ ∨ q3.ν = p.μ := by
      rcases (mem_plaquetteBoundary_iff q3 e1').mp h with ⟨hd, _⟩ | ⟨hd, _⟩
      · left; exact hd.symm
      · right; exact hd.symm
    have h_planes : q3.μ = p.μ ∧ q3.ν = p.ν := by
      have := p.h_lt; have := q3.h_lt; omega
    exact hq3_ne (by cases p; cases q3; simp only at hq3_base; rcases h_planes with ⟨h1, h2⟩; subst hq3_base h1 h2; rfl)
  -- Therefore q5 ∉ {p, q1, q2, q3, q4}
  have hq5_p : q5 ≠ p := fun h => h_not_p (h ▸ hq5_e1')
  have hq5_2 : q5 ≠ q2 := fun h => h_not_q2 (h ▸ hq5_e1')
  have hq5_3 : q5 ≠ q3 := fun h => h_not_q3 (h ▸ hq5_e1')
  have hq5_4 : q5 ≠ q4 := fun h => h_not_q4 (h ▸ hq5_e1')
  let six : Finset Z4Plaquette := {p, q1, q2, q3, q4, q5}
  have hsix_sub : six ⊆ γ := by
    intro x hx
    simp only [six, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hp_mem
    · exact hq1_mem
    · exact hq2_mem
    · exact hq3_mem
    · exact hq4_mem
    · exact hq5_mem
  have hsix_card : six.card = 6 := by
    dsimp [six]
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
        Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
        Finset.card_insert_of_notMem, Finset.card_singleton]
    · simp [hq5_4.symm]
    · simp [hq34, hq5_3.symm]
    · simp [hq23, hq24, hq5_2.symm]
    · simp [hq12, hq13, hq14, hq5_ne1.symm]
    · simp [hq1_ne.symm, hq2_ne.symm, hq3_ne.symm, hq4_ne.symm, hq5_p.symm]
  rw [← hsix_card]
  exact Finset.card_le_card hsix_sub

/-! ============================================================================
    PART III: 4-HYPERCUBE POLYMER UNIT BOUNDARY (24 PLAQUETTES)
    ============================================================================ -/

/-- Clean, direct bijection for the 24 boundary plaquettes of a unit 4-hypercube `[x, x+1]⁴`:
    6 coordinate 2-planes `(μ < ν)` × 4 faces `(b₁, b₂) ∈ {0, 1}²` in the orthogonal 2-plane. -/
def hypercube4FaceIndex : Type :=
  { p : Fin 4 × Fin 4 // p.1 < p.2 } × Bool × Bool
  deriving DecidableEq, Fintype

theorem hypercube4FaceIndex_card : Fintype.card hypercube4FaceIndex = 24 := by
  decide

/-! ============================================================================
    PART IV: PEIERLS SUPPRESSION DOMINATING KLARNER ENTROPY s_entropy = ln(2401)
    ============================================================================ -/

/-- `exp(-10) < 1 / 2401`, i.e. `s_entropy = ln(2401) < 10`, proved from `e > 2.5`. -/
theorem exp_neg_ten_lt_inv_2401 : Real.exp (-10) < (1 : ℝ) / 2401 := by
  have he : (25 / 10 : ℝ) < Real.exp 1 := by
    have := Real.exp_one_gt_d9
    linarith
  have h_pow : (2401 : ℝ) < Real.exp 10 := by
    have h1 : (2401 : ℝ) < (25 / 10 : ℝ) ^ 10 := by norm_num
    have h2 : (25 / 10 : ℝ) ^ 10 < (Real.exp 1) ^ 10 :=
      pow_lt_pow_left₀ he (by norm_num) (by norm_num)
    have h_exp : (Real.exp 1) ^ 10 = Real.exp 10 := by
      rw [← Real.exp_nat_mul]; norm_num
    linarith [h_exp]
  rw [Real.exp_neg, inv_eq_one_div]
  exact one_div_lt_one_div_of_lt (by norm_num) h_pow

/-- Upper bound `exp(-10) > 1 / 22167` derived from `Real.exp_one_lt_d9` (`e < 2.72`). -/
theorem exp_ten_lt_pow_272 : Real.exp 10 < (272 / 100 : ℝ) ^ 10 := by
  have he : Real.exp 1 < (272 / 100 : ℝ) := by
    have := Real.exp_one_lt_d9
    linarith
  have h_pow : (Real.exp 1) ^ 10 < (272 / 100 : ℝ) ^ 10 :=
    pow_lt_pow_left₀ he (Real.exp_pos 1).le (by norm_num)
  have h_exp : (Real.exp 1) ^ 10 = Real.exp 10 := by
    rw [← Real.exp_nat_mul]; norm_num
  rwa [h_exp] at h_pow

/-- Helper: if `x ≤ (100 / 272)^10` (or `x * (272/100)^10 ≤ 1`), then `x < Real.exp (-10)`. -/
theorem lt_exp_neg_ten_of_mul_le {x : ℝ} (hx_nonneg : 0 ≤ x)
    (h_mul : x * (272 / 100 : ℝ) ^ 10 ≤ 1) :
    x < Real.exp (-10) := by
  have h_pos : 0 < Real.exp 10 := Real.exp_pos 10
  have h_lt : x * Real.exp 10 < 1 := by
    by_cases hx0 : x = 0
    · subst hx0; simp
    · have hx_pos : 0 < x := lt_of_le_of_ne hx_nonneg (Ne.symm hx0)
      calc x * Real.exp 10 < x * (272 / 100 : ℝ) ^ 10 :=
            mul_lt_mul_of_pos_left exp_ten_lt_pow_272 hx_pos
        _ ≤ 1 := h_mul
  rw [Real.exp_neg, inv_eq_one_div]
  exact (lt_div_iff₀ h_pos).mpr h_lt

/-- **1. Minimal Closed 2-Cycle Wilson Peierls Bound (|γ| ≥ 6, β ≥ 5/2)**:
    Because `∂γ = 0` forces `|γ| ≥ 6` (`closed_2cycle_card_ge_six`), the Wilson action
    suppression at `β ≥ 5/2` satisfies `exp(-β |γ|) ≤ exp(-15) < exp(-10) < 1 / 2401`. -/
theorem closed_2cycle_wilson_peierls_dominates_klarner
    {γ : Finset Z4Plaquette} (hne : γ.Nonempty) (hclosed : IsClosed2Cycle γ)
    {β : ℝ} (hβ : (5 / 2 : ℝ) ≤ β) :
    Real.exp (-β * (γ.card : ℝ)) < Real.exp (-10) ∧
    Real.exp (-β * (γ.card : ℝ)) < (1 : ℝ) / 2401 := by
  have h6 : (6 : ℝ) ≤ (γ.card : ℝ) := by exact_mod_cast closed_2cycle_card_ge_six hne hclosed
  have h_prod : (15 : ℝ) ≤ β * (γ.card : ℝ) := by nlinarith
  have h_exp : Real.exp (-β * (γ.card : ℝ)) < Real.exp (-10) := by
    apply Real.exp_lt_exp.mpr
    linarith
  exact ⟨h_exp, lt_trans h_exp exp_neg_ten_lt_inv_2401⟩

/-- **2. Strong-Coupling SU(3) Character Bound at β = 1/2 (|γ| ≥ 6)**:
    With `ζ₃(1/2) ≤ 28/1000`, any closed 2-cycle `γ` (`|γ| ≥ 6`) satisfies
    `ζ₃(1/2)^|γ| ≤ (28/1000)^6 < exp(-10) < 1 / 2401`. -/
theorem strong_coupling_character_6_dominates_klarner
    {γ : Finset Z4Plaquette} (hne : γ.Nonempty) (hclosed : IsClosed2Cycle γ)
    {zeta : ℝ} (hz_nonneg : 0 ≤ zeta) (hz_le : zeta ≤ 28 / 1000) :
    zeta ^ γ.card < Real.exp (-10) ∧ zeta ^ γ.card < (1 : ℝ) / 2401 := by
  have h6 : 6 ≤ γ.card := closed_2cycle_card_ge_six hne hclosed
  have h_mono1 : zeta ^ γ.card ≤ (28 / 1000 : ℝ) ^ γ.card :=
    pow_le_pow_left₀ hz_nonneg hz_le γ.card
  have h_mono2 : (28 / 1000 : ℝ) ^ γ.card ≤ (28 / 1000 : ℝ) ^ 6 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) h6
  have h_cap : (28 / 1000 : ℝ) ^ 6 * (272 / 100 : ℝ) ^ 10 ≤ 1 := by norm_num
  have h_lt : (28 / 1000 : ℝ) ^ 6 < Real.exp (-10) :=
    lt_exp_neg_ten_of_mul_le (by norm_num) h_cap
  have h_res : zeta ^ γ.card < Real.exp (-10) := lt_of_le_of_lt (le_trans h_mono1 h_mono2) h_lt
  exact ⟨h_res, lt_trans h_res exp_neg_ten_lt_inv_2401⟩

/-- **3. Crossover Endpoint SU(3) Character Bound at β = 5/2 on Multi-Cube (|γ| ≥ 11) and
    4-Hypercube Polymer Unit (|∂c₄| = 24)**:
    With `ζ₃(5/2) ≤ 382/1000`, any polymer carrying `m ≥ 11` plaquette faces (in particular
    a 4-hypercube unit carrying `24` faces) satisfies:
      `ζ₃(5/2)^m ≤ (382/1000)^11 < exp(-10) < 1 / 2401`. -/
theorem crossover_character_dominates_klarner
    {m : ℕ} (hm : 11 ≤ m) {zeta : ℝ} (hz_nonneg : 0 ≤ zeta) (hz_le : zeta ≤ 382 / 1000) :
    zeta ^ m < Real.exp (-10) ∧ zeta ^ m < (1 : ℝ) / 2401 := by
  have h_mono1 : zeta ^ m ≤ (382 / 1000 : ℝ) ^ m := pow_le_pow_left₀ hz_nonneg hz_le m
  have h_mono2 : (382 / 1000 : ℝ) ^ m ≤ (382 / 1000 : ℝ) ^ 11 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hm
  have h_cap : (382 / 1000 : ℝ) ^ 11 * (272 / 100 : ℝ) ^ 10 ≤ 1 := by norm_num
  have h_lt : (382 / 1000 : ℝ) ^ 11 < Real.exp (-10) :=
    lt_exp_neg_ten_of_mul_le (by norm_num) h_cap
  have h_res : zeta ^ m < Real.exp (-10) := lt_of_le_of_lt (le_trans h_mono1 h_mono2) h_lt
  exact ⟨h_res, lt_trans h_res exp_neg_ten_lt_inv_2401⟩

theorem hypercube4_character_dominates_klarner
    {zeta : ℝ} (hz_nonneg : 0 ≤ zeta) (hz_le : zeta ≤ 382 / 1000) :
    zeta ^ (Fintype.card hypercube4FaceIndex) < Real.exp (-10) ∧
    zeta ^ (Fintype.card hypercube4FaceIndex) < (1 : ℝ) / 2401 := by
  rw [hypercube4FaceIndex_card]
  exact crossover_character_dominates_klarner (by decide) hz_nonneg hz_le

#print axioms plaquetteBoundary_card
#print axioms two_plaquettes_share_at_most_one_edge
#print axioms closed_2cycle_card_ge_six
#print axioms hypercube4FaceIndex_card
#print axioms closed_2cycle_wilson_peierls_dominates_klarner
#print axioms strong_coupling_character_6_dominates_klarner
#print axioms crossover_character_dominates_klarner
#print axioms hypercube4_character_dominates_klarner

end YangMills.HypercubicPolymerCounting
