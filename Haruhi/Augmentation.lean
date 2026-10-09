/-
Copyright (c) 2026 Uku Raudvere. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted from Hunter.ProofsPu.pu_exists_with_verts, commit
 d45222190031d162feb1f6f3cf5fe2d11fab726d.
The extension accepts any external predecessor, not only a cheapest one.
-/
import Hunter.ProofsPu
import PreimageChain.ComponentGeometry

namespace Haruhi
open List Hunter Hunter.HPath Hunter.ProofsPu
open scoped Classical
variable {k : ℕ}

/-- Prepend the entire rotation class of an arbitrary external predecessor.
The exact connecting edge weight is retained. -/
theorem prepend_orbit_exists_with_verts (hk : 2 ≤ k) {p : HPath k} (hSE : p.StronglyExitless)
    {u : Vtx k} (hu : u ∉ p.verts) :
    ∃ q : HPath k, q.verts = orbitList (sigma u) ++ p.verts ∧
      q.Exitless ∧ q.numVerts = p.numVerts + k ∧
      q.wtP = (k - 1) + ew k u p.first + p.wtP := by
  have hk1 : 1 ≤ k := by omega
  set N := p.numVerts with hNdef
  have hpe : p.Exitless := hSE.1
  have huoc : p.IsUnionOfCycles := Proved.clm_1cyclesubset hSE
  -- every orbit vertex has `rotClass u`
  have hrc : ∀ i, rotClass ((sigma^[i] (sigma u)).1) = rotClass u.1 := fun i => by
    rw [ProofsExitless.rotClass_sigma_iter i (sigma u), ProofsStructure.rotClass_sigma u]
  -- a vertex of `p` never lies in the orbit (its `σ`-cycle would drag `u` into `p`)
  have hpin : ∀ x : Vtx k, x ∈ p.verts → x ∉ orbitList (sigma u) := by
    intro x hx hxo
    obtain ⟨i, -, rfl⟩ := mem_orbitList hxo
    have hcyc : u ∈ cyc (sigma^[i] (sigma u)) := ProofsExitless.mem_cyc.mpr (hrc i).symm
    exact hu (HPath.mem_vertsFinset.mp (huoc _ hx hcyc))
  -- build the path `q`
  have hnodup : (orbitList (sigma u) ++ p.verts).Nodup := by
    rw [List.nodup_append]
    refine ⟨orbitList_nodup hk1 (sigma u), p.nodup, ?_⟩
    intro a ha b hb heq
    exact hpin b hb (heq ▸ ha)
  have hne : orbitList (sigma u) ++ p.verts ≠ [] := by
    simp only [ne_eq, List.append_eq_nil_iff, not_and]; intro _; exact p.ne
  set q : HPath k := ⟨orbitList (sigma u) ++ p.verts, hne, hnodup⟩ with hqdef
  have hqverts : q.verts = orbitList (sigma u) ++ p.verts := rfl
  have hpvl : p.verts.length = N := rfl
  have hqnv : q.numVerts = p.numVerts + k := by
    show (orbitList (sigma u) ++ p.verts).length = p.numVerts + k
    rw [List.length_append, orbitList_length, hpvl]; omega
  -- vertex access
  have hvo : ∀ i, i < k → q.vert i = sigma^[i] (sigma u) := by
    intro i hi
    have hi' : i < (orbitList (sigma u)).length := by rw [orbitList_length]; exact hi
    have hval : q.vert i = (orbitList (sigma u) ++ p.verts)[i]'(by
        rw [List.length_append]; omega) := by
      rw [ProofsExitless.vert_getElem q (by rw [hqnv]; omega)]; rfl
    rw [hval, List.getElem_append_left hi', orbitList_getElem (sigma u) hi']
  have hvp : ∀ t, t < N → q.vert (k + t) = p.vert t := by
    intro t ht
    have hlen : (orbitList (sigma u)).length ≤ k + t := by rw [orbitList_length]; omega
    have hval : q.vert (k + t) = (orbitList (sigma u) ++ p.verts)[k + t]'(by
        rw [List.length_append, orbitList_length, hpvl]; omega) := by
      rw [ProofsExitless.vert_getElem q (by rw [hqnv]; omega)]; rfl
    rw [hval, List.getElem_append_right hlen,
      ProofsExitless.vert_getElem p (show t < p.numVerts from ht)]
    congr 1
    rw [orbitList_length]; omega
  -- position of a `p`-vertex inside `q` is shifted by `k`
  have hpos : ∀ v : Vtx k, v ∈ p.verts → q.pos v = k + p.pos v := by
    intro v hv
    show (orbitList (sigma u) ++ p.verts).idxOf v = k + p.verts.idxOf v
    rw [List.idxOf_append_of_notMem (hpin v hv), orbitList_length]
  -- `σ^{k-1}(σu) = u`
  have hlast : sigma^[k - 1] (sigma u) = u := by
    have h1 : sigma u = sigma^[1] u := by rw [Function.iterate_one]
    rw [h1, ← Function.iterate_add_apply sigma (k - 1) 1 u, show k - 1 + 1 = k from by omega,
      ProofsExitless.sigma_iter_period u]
  -- the junction weight is `ew k u p.first`; the orbit steps are weight 1
  refine ⟨q, hqverts, ?_, hqnv, ?_⟩
  · -- Exitless
    rw [HPath.Exitless]
    rintro ⟨i, hi1, hw, hlt⟩
    rw [hqnv] at hi1
    rcases lt_trichotomy (i + 1) k with hc1 | hc2 | hc3
    · -- both endpoints in the orbit: weight-1 σ-step
      have hik : i < k := by omega
      have hik1 : i + 1 < k := hc1
      rw [hvo i hik, hvo (i + 1) hik1,
        show sigma^[i + 1] (sigma u) = sigma (sigma^[i] (sigma u)) from
          (Function.iterate_succ_apply' sigma i (sigma u)),
        ew_sigma hk1] at hw
      omega
    · -- junction `i = k-1`: `σ(q[k-1]) = σu = q[0]`, position 0
      have hik : i < k := by omega
      have hiv : q.vert i = u := by
        rw [hvo i hik, show i = k - 1 from by omega, hlast]
      have hs : sigma (q.vert i) = q.vert 0 := by
        rw [hiv, hvo 0 hk1]; simp [Function.iterate_zero]
      rw [hs, ProofsExitless.pos_vert q (by rw [hqnv]; omega)] at hlt
      omega
    · -- inside `p`: shift by `k`, use `p`'s exitless rule
      obtain ⟨t, rfl⟩ : ∃ t, i = k + t := ⟨i - k, by omega⟩
      have htN : t + 1 < N := by omega
      have htN' : t < N := by omega
      rw [hvp t htN', show k + t + 1 = k + (t + 1) from by ring, hvp (t + 1) htN] at hw
      -- σ(p[t]) ∈ p.verts
      have hpvt : p.vert t ∈ p.verts := ProofsExitless.vert_mem p htN'
      have hsv : sigma (p.vert t) ∈ p.verts := by
        have hcyc : sigma (p.vert t) ∈ cyc (p.vert t) :=
          ProofsExitless.mem_cyc.mpr (ProofsStructure.rotClass_sigma (p.vert t))
        exact HPath.mem_vertsFinset.mp (huoc _ hpvt hcyc)
      rcases ProofsExitless.exitless_step hk1 hpe htN with heq | hle
      · rw [heq, ew_sigma hk1] at hw; omega
      · have hqs : sigma (q.vert (k + t)) = sigma (p.vert t) := by rw [hvp t htN']
        rw [hqs, hpos _ hsv] at hlt
        omega
  · -- weight
    rw [Proved.wtP_eq_sum q, hqnv]
    -- split `range (p.numVerts + k - 1)` at `k`
    have hsplit : Finset.range (p.numVerts + k - 1)
        = Finset.range k ∪ Finset.Ico k (p.numVerts + k - 1) := by
      rw [Finset.range_eq_Ico, Finset.range_eq_Ico,
        Finset.Ico_union_Ico_eq_Ico (Nat.zero_le k) (by have := p.numVerts_pos; omega)]
    have hdisj : Disjoint (Finset.range k) (Finset.Ico k (p.numVerts + k - 1)) := by
      rw [Finset.range_eq_Ico]; exact Finset.Ico_disjoint_Ico_consecutive 0 k _
    rw [hsplit, Finset.sum_union hdisj]
    -- Part 1: orbit + junction = (k-1) + ew k u p.first
    have hpart1 : ∑ i ∈ Finset.range k, ew k (q.vert i) (q.vert (i + 1))
        = (k - 1) + ew k u p.first := by
      have hrange : ∑ i ∈ Finset.range k, ew k (q.vert i) (q.vert (i + 1))
          = ∑ i ∈ Finset.range ((k - 1) + 1), ew k (q.vert i) (q.vert (i + 1)) := by
        rw [show (k - 1) + 1 = k from by omega]
      rw [hrange, Finset.sum_range_succ]
      have horbstep : ∀ i ∈ Finset.range (k - 1), ew k (q.vert i) (q.vert (i + 1)) = 1 := by
        intro i hi
        rw [Finset.mem_range] at hi
        have hik : i < k := by omega
        have hik1 : i + 1 < k := by omega
        rw [hvo i hik, hvo (i + 1) hik1,
          show sigma^[i + 1] (sigma u) = sigma (sigma^[i] (sigma u)) from
            (Function.iterate_succ_apply' sigma i (sigma u)), ew_sigma hk1]
      rw [Finset.sum_congr rfl horbstep, Finset.sum_const, Finset.card_range, smul_eq_mul,
        mul_one]
      -- junction term
      have hjunc : ew k (q.vert (k - 1)) (q.vert (k - 1 + 1)) = ew k u p.first := by
        have h1 : q.vert (k - 1) = u := by rw [hvo (k - 1) (by omega), hlast]
        have h2 : q.vert (k - 1 + 1) = p.first := by
          rw [show k - 1 + 1 = k + 0 from by omega, hvp 0 p.numVerts_pos, HPath.vert_zero]
        rw [h1, h2]
      rw [hjunc]
    -- Part 2: inside `p` = wtP p
    have hpart2 : ∑ i ∈ Finset.Ico k (p.numVerts + k - 1), ew k (q.vert i) (q.vert (i + 1))
        = p.wtP := by
      rw [Finset.sum_Ico_eq_sum_range]
      rw [show p.numVerts + k - 1 - k = p.numVerts - 1 from by omega]
      rw [Proved.wtP_eq_sum p]
      apply Finset.sum_congr rfl
      intro t ht
      rw [Finset.mem_range] at ht
      have htN' : t < N := by omega
      have htN : t + 1 < N := by omega  -- from t < p.numVerts - 1
      rw [hvp t htN', show k + t + 1 = k + (t + 1) from by ring, hvp (t + 1) htN]
    rw [hpart1, hpart2]


/-- The augmented path still consists of complete rotation classes. -/
theorem prepend_orbit_strong_exists (hk : 2 ≤ k) {p : HPath k}
    (hp : p.StronglyExitless) {u : Vtx k} (hu : u ∉ p.verts) :
    ∃ q : HPath k,
      q.verts = orbitList (sigma u) ++ p.verts ∧
      q.StronglyExitless ∧ q.numVerts = p.numVerts + k ∧
      q.wtP = (k - 1) + ew k u p.first + p.wtP ∧
      q.last = p.last := by
  obtain ⟨q, hv, he, hn, hw⟩ := prepend_orbit_exists_with_verts hk hp hu
  have hl : q.last = p.last := by
    unfold HPath.last
    simp only [hv, List.getLast_append_right p.ne]
  have hstrong : q.StronglyExitless := by
    refine ⟨he, ?_⟩
    rw [hl, hv]
    exact List.mem_append_right _ hp.2
  exact ⟨q, hv, hstrong, hn, hw, hl⟩

/-- Prepending one full rotation class increases the exact block count by one. -/
theorem prepend_orbit_classCount (hk : 1 ≤ k) {p q : HPath k}
    (hn : q.numVerts = p.numVerts + k) :
    PreimageChain.componentClassCount q =
      PreimageChain.componentClassCount p + 1 := by
  unfold PreimageChain.componentClassCount
  rw [hn, Nat.add_div_right _ (by omega : 0 < k)]

end Haruhi
