import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.CleanedNonEdge PEqualNP.EdgeOwnership

set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_3527_703
    (normalize : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      G.edgeFinset.Nonempty → IsLeastAO G C →
      ∃ D : Circuit, IsLeastAO G D ∧ D.size = C.size ∧
        (junk G D).card = (junk G C).card ∧ TopForm G D)
    (charge : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      NoFourCycle G → G.edgeFinset.Nonempty → IsLeastAO G C → TopForm G C →
      G.edgeFinset.card + (tops G C \ centreless G C).card + 2 * (centreless G C).card +
        (junk G C).card + (orN G C \ lam G C).card ≤ C.size + (Ustar G C).card + 1 ∧
      ∀ K : Finset (Fin n), IsMinCover (G.deleteEdges ↑(Ustar G C)) K →
        K.card ≤ (tops G C \ centreless G C).card)
    (residual_ge2 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      G.IsBipartite → NoFourCycle G → ¬ G.IsAcyclic → IsLeastAO G C → TopForm G C →
      2 ≤ (junk G C).card →
      let U := Ustar G C
      U.Nonempty → ∃ K X : Finset (Fin n), IsMinCover (G.deleteEdges ↑U) K ∧
        (∀ e ∈ U, ∃ v ∈ K ∪ X, v ∈ e) ∧
        (K ∪ X).card + U.card ≤ (tops G C \ centreless G C).card +
          2 * (centreless G C).card + (junk G C).card + (orN G C \ lam G C).card)
    (compileStars : ∀ (n m : ℕ) (E : Finset (Fin n × Fin m)) (T : Finset (Fin (n + m))),
      (∀ e ∈ E, Fin.castAdd m e.1 ∈ T ∨ Fin.natAdd n e.2 ∈ T) →
      ∃ D : Circuit, IsAO2 (n + m) D ∧ D.size ≤ E.card + T.card - 1 ∧
        ∀ x : Fin (n + m) → Bool, circuitFun (n + m) D x =
          decide (∃ p l, (p, l) ∈ E ∧ x (Fin.castAdd m p) = true ∧ x (Fin.natAdd n l) = true)) :
∀ (x1 x2 : ℕ) (x3 x4 : Finset (Fin x1 × Fin x2)) (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 : SimpleGraph (Fin (x1 + x2))), (∀ (x7 x8 : Fin (x1 + x2)), x6.Adj x7 x8 ↔ ∃ x9 ∈ x3, x7 = Fin.castAdd x2 x9.1 ∧ x8 = Fin.natAdd x1 x9.2 ∨ x8 = Fin.castAdd x2 x9.1 ∧ x7 = Fin.natAdd x1 x9.2) → ¬x6.IsAcyclic → (∀ (x9 x10 : Fin x1) (x11 x12 : Fin x2), x9 ≠ x10 → x11 ≠ x12 → ¬((x9, x11) ∈ x3 ∧ (x9, x12) ∈ x3 ∧ (x10, x11) ∈ x3 ∧ (x10, x12) ∈ x3)) → PEqualNP.TopForm.IsAO2 (x1 + x2) x5 → (∀ (x11 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x5 x11 = Decidable.decide (∃ (x12 : Fin x1) (x13 : Fin x2), (x12, x13) ∈ x3 ∧ x11 (Fin.castAdd x2 x12) = Bool.true ∧ x11 (Fin.natAdd x1 x13) = Bool.true)) → x4 ⊆ x3 → (∀ x13 ∈ x4, ∀ x15 ∈ x4, x13.1 = x15.1 → x13 = x15) → (∀ x14 ∈ x4, ∀ x16 ∈ x4, x14.2 = x16.2 → x14 = x16) → ∃ x15 ∈ x3, x15 ∉ x4 ∧ ∃ (x16 : PEqualNP.CircuitLowerBounds.Circuit), x16.size < x5.size ∧ PEqualNP.TopForm.IsAO2 (x1 + x2) x16 ∧ ∀ (x17 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x16 x17 = Decidable.decide (∃ (x18 : Fin x1) (x19 : Fin x2), (x18, x19) ∈ x3.erase x15 ∧ x17 (Fin.castAdd x2 x18) = Bool.true ∧ x17 (Fin.natAdd x1 x19) = Bool.true) := by
  classical
  intro n m E M C G hG hcyc h4 hC hfun _hsub hleft hright
  let L : Fin n → Fin (n + m) := Fin.castAdd m
  let R : Fin m → Fin (n + m) := Fin.natAdd n
  have hcross (p : Fin n) (l : Fin m) : L p ≠ R l := by
    intro h
    have hh := congrArg Fin.val h
    change p.val = n + l.val at hh
    have := p.isLt
    omega
  have hL : Function.Injective L := by
    intro a b hab
    have hh := congrArg (fun z : Fin (n + m) => z.val) hab
    exact Fin.ext hh
  have hR : Function.Injective R := by
    intro a b hab
    have hh := congrArg Fin.val hab
    change n + a.val = n + b.val at hh
    exact Fin.ext (by omega)
  have side (v : Fin (n + m)) : (∃ p, v = L p) ∨ ∃ l, v = R l := by
    by_cases hv : v.val < n
    · exact Or.inl ⟨⟨v.val, hv⟩, Fin.ext rfl⟩
    · refine Or.inr ⟨⟨v.val - n, by have := v.isLt; omega⟩, ?_⟩
      apply Fin.ext
      change v.val = n + (v.val - n)
      omega
  have adjL (p : Fin n) (v : Fin (n + m)) :
      G.Adj (L p) v ↔ ∃ l, (p, l) ∈ E ∧ v = R l := by
    rw [hG]
    constructor
    · rintro ⟨e, he, ⟨hp, hv⟩ | ⟨_, hp⟩⟩
      · have hh := hL hp
        exact ⟨e.2, by simpa only [hh] using he, hv⟩
      · exact False.elim (hcross _ _ hp)
    · rintro ⟨l, he, rfl⟩
      exact ⟨(p, l), he, Or.inl ⟨rfl, rfl⟩⟩
  have adjR (l : Fin m) (v : Fin (n + m)) :
      G.Adj (R l) v ↔ ∃ p, (p, l) ∈ E ∧ v = L p := by
    rw [hG]
    constructor
    · rintro ⟨e, he, ⟨hl, _⟩ | ⟨hv, hl⟩⟩
      · exact False.elim (hcross _ _ hl.symm)
      · have hh := hR hl
        exact ⟨e.1, by simpa only [hh] using he, hv⟩
    · rintro ⟨p, he, rfl⟩
      exact ⟨(p, l), he, Or.inr ⟨rfl, rfl⟩⟩
  have incidence (p : Fin n) (l : Fin m) : G.Adj (L p) (R l) ↔ (p, l) ∈ E := by
    rw [adjL]
    constructor
    · rintro ⟨l', he, hl⟩
      rwa [← hR hl] at he
    · exact fun he => ⟨l, he, rfl⟩
  have eligible : ∃ e ∈ E, e ∉ M := by
    by_contra! hnone
    have single {u v w : Fin (n + m)} (huv : G.Adj u v) (huw : G.Adj u w) : v = w := by
      rcases side u with ⟨p, rfl⟩ | ⟨l, rfl⟩
      · obtain ⟨a, ha, rfl⟩ := (adjL p v).mp huv
        obtain ⟨b, hb, rfl⟩ := (adjL p w).mp huw
        have key := hleft (p, a) (hnone _ ha) (p, b) (hnone _ hb) rfl
        exact congrArg (fun e : Fin n × Fin m => R e.2) key
      · obtain ⟨a, ha, rfl⟩ := (adjR l v).mp huv
        obtain ⟨b, hb, rfl⟩ := (adjR l w).mp huw
        have key := hright (a, l) (hnone _ ha) (b, l) (hnone _ hb) rfl
        exact congrArg (fun e : Fin n × Fin m => L e.1) key
    apply hcyc
    intro u w hw
    have enough := hw.three_le_length
    have h₀ := w.adj_getVert_succ (i := 0) (by omega)
    have h₁ := w.adj_getVert_succ (i := 1) (by omega)
    have eq := single h₀.symm h₁
    have hn : (0 : ℕ) = 2 := hw.getVert_injOn' (by simp) (by change 2 ≤ w.length - 1; omega) eq
    omega
  obtain ⟨e, he, heM⟩ := eligible
  have hNo4 : NoFourCycle G := by
    intro a b hab
    apply Finset.card_le_one.mpr
    intro c hc d hd
    obtain ⟨hac, hbc⟩ := (Finset.mem_filter.mp hc).2
    obtain ⟨had, hbd⟩ := (Finset.mem_filter.mp hd).2
    by_contra hcd
    rcases side a with ⟨p, rfl⟩ | ⟨l, rfl⟩
    · obtain ⟨l, hpl, rfl⟩ := (adjL p c).mp hac
      obtain ⟨r, hpr, rfl⟩ := (adjL p d).mp had
      obtain ⟨q, hql, rfl⟩ := (adjR l b).mp hbc.symm
      exact h4 p q l r (fun h => hab (congrArg L h)) (fun h => hcd (congrArg R h))
        ⟨hpl, hpr, hql, (incidence q r).mp hbd⟩
    · obtain ⟨p, hpl, rfl⟩ := (adjR l c).mp hac
      obtain ⟨q, hql, rfl⟩ := (adjR l d).mp had
      obtain ⟨r, hpr, rfl⟩ := (adjL p b).mp hbc.symm
      exact h4 p q l r (fun h => hcd (congrArg L h)) (fun h => hab (congrArg R h))
        ⟨hpl, hpr, hql, (incidence q r).mp hbd.symm⟩
  have hBip : G.IsBipartite := by
    apply SimpleGraph.isBipartite_iff_exists_isBipartiteWith.mpr
    refine ⟨Set.range L, Set.range R, Set.disjoint_left.mpr ?_, ?_⟩
    · rintro _ ⟨p, rfl⟩ ⟨l, hl⟩
      exact hcross p l hl.symm
    · intro a b hab
      rcases (hG a b).mp hab with ⟨d, _, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
      · exact Or.inl ⟨⟨d.1, rfl⟩, ⟨d.2, rfl⟩⟩
      · exact Or.inr ⟨⟨d.2, rfl⟩, ⟨d.1, rfl⟩⟩
  let edge : Fin n × Fin m → Sym2 (Fin (n + m)) := fun d => s(L d.1, R d.2)
  have edge_inj : Function.Injective edge := by
    intro a b h
    rcases Sym2.eq_iff.mp h with ⟨ha, hb⟩ | ⟨ha, _⟩
    · exact Prod.ext (hL ha) (hR hb)
    · exact False.elim (hcross _ _ ha)
  let _ : DecidableRel G.Adj := Classical.decRel _
  have edgeFinset_eq : G.edgeFinset = E.image edge := by
    ext z
    refine Sym2.ind ?_ z
    intro u v
    simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, Finset.mem_image, edge,
      Sym2.eq_iff, hG]
    constructor
    · rintro ⟨d, hd, ⟨hu, hv⟩ | ⟨hv, hu⟩⟩
      · exact ⟨d, hd, Or.inl ⟨hu.symm, hv.symm⟩⟩
      · exact ⟨d, hd, Or.inr ⟨hv.symm, hu.symm⟩⟩
    · rintro ⟨d, hd, ⟨hu, hv⟩ | ⟨hv, hu⟩⟩
      · exact ⟨d, hd, Or.inl ⟨hu.symm, hv.symm⟩⟩
      · exact ⟨d, hd, Or.inr ⟨hv.symm, hu.symm⟩⟩
  have hEdges : G.edgeFinset.Nonempty := by
    rw [edgeFinset_eq]
    exact ⟨edge e, Finset.mem_image_of_mem edge he⟩
  have hcard : G.edgeFinset.card = E.card := by
    rw [edgeFinset_eq, Finset.card_image_of_injective _ edge_inj]
  have computes : circuitFun (n + m) C = graphFun G ∅ := by
    funext x
    change circuitFun (n + m) C x =
      (decide (∃ a ∈ (∅ : Finset (Fin (n + m))), x a = true) ||
        decide (∃ u v, G.Adj u v ∧ x u = true ∧ x v = true))
    rw [hfun, Bool.eq_iff_iff]
    simp only [Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or,
      decide_eq_true_iff]
    constructor
    · rintro ⟨p, l, hp, hx, hy⟩
      exact ⟨L p, R l, (incidence p l).mpr hp, hx, hy⟩
    · rintro ⟨u, v, hu, hx, hy⟩
      rcases (hG u v).mp hu with ⟨d, hd, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
      · exact ⟨d.1, d.2, hd, hx, hy⟩
      · exact ⟨d.1, d.2, hd, hy, hx⟩
  let conjecture (s : ℕ) := ∃ D : Circuit, IsAO2 (n + m) D ∧ circuitFun (n + m) D = graphFun G ∅ ∧ D.size = s
  have existsSize : ∃ s, conjecture s := ⟨C.size, C, hC, computes, rfl⟩
  obtain ⟨Cmin, hCmin, heval, hsz⟩ := Nat.find_spec existsSize
  have hLeast : IsLeastAO G Cmin := ⟨hCmin, heval, fun D hD hDval =>
    hsz ▸ Nat.find_min' existsSize (show conjecture D.size from ⟨D, hD, hDval, rfl⟩)⟩
  have hmin : Cmin.size ≤ C.size := hLeast.2.2 C hC computes
  obtain ⟨D, hDleast, hDsize, _, hDtop⟩ := normalize (n + m) G Cmin hEdges hLeast
  have hc := (charge (n + m) G D hNo4 hEdges hDleast hDtop).1

  have hExtension : ∃ K X : Finset (Fin (n + m)), IsMinCover (G.deleteEdges ↑(Ustar G D)) K ∧
      (∀ e ∈ Ustar G D, ∃ v ∈ K ∪ X, v ∈ e) ∧
      (K ∪ X).card + (Ustar G D).card ≤ (tops G D \ centreless G D).card +
        2 * (centreless G D).card + (junk G D).card + (orN G D \ lam G D).card := by
    by_cases hU : (Ustar G D).Nonempty
    · by_cases hj2 : 2 ≤ (junk G D).card
      · exact residual_ge2 (n + m) G D hBip hNo4 hcyc hDleast hDtop hj2 hU
      · clear normalize residual_ge2 _hsub hleft hright hcyc
        have hDAO : IsAO2 (n + m) D := hDleast.1
        have hDeval : circuitFun (n + m) D = graphFun G ∅ := hDleast.2.1
        let N := n + m
        have hgateAt_D : ∀ k (hk : k < D.gates.length), gateAt D k = D.gates[k]'hk := fun k hk => by
          unfold gateAt; simp [List.getD_eq_getElem?_getD, hk]
        have hgateAt_D_mem : ∀ k (hk : k < D.gates.length), gateAt D k ∈ D.gates := fun k hk => by
          rw [hgateAt_D k hk]; exact List.getElem_mem hk
        have hgateAt_D_len2 : ∀ k (hk : k < D.gates.length), (gateAt D k).inputs.length = 2 := fun k hk =>
          hDAO.2.2 _ (hgateAt_D_mem k hk)
        have hopnd_D_mem : ∀ k (hk : k < D.gates.length) (b : Fin 2), opnd D k b ∈ (gateAt D k).inputs := fun k hk b => by
          have hlen2 := hgateAt_D_len2 k hk
          have hb : (b : ℕ) < (gateAt D k).inputs.length := by rw [hlen2]; exact b.isLt
          unfold opnd; simp [hb, List.getElem_mem]
        have hopnd_D_lt : ∀ k (hk : k < D.gates.length) (b : Fin 2), opnd D k b < N + k := fun k hk b =>
          hDAO.2.1 k hk (opnd D k b) (hopnd_D_mem k hk b)
        have hgateAt_D_inputs : ∀ k (hk : k < D.gates.length), (gateAt D k).inputs = [opnd D k 0, opnd D k 1] := fun k hk => by
          have hlen2 := hgateAt_D_len2 k hk
          rcases hlist : (gateAt D k).inputs with _ | ⟨a0, _ | ⟨a1, _ | _⟩⟩
          · rw [hlist] at hlen2; cases hlen2
          · rw [hlist] at hlen2; cases hlen2
          · unfold opnd; simp only [hlist, List.getD_cons_zero, List.getD_cons_succ]; rfl
          · rw [hlist] at hlen2; cases hlen2
        have orSets_len : ∀ (gs : List Gate) (acc : List (List ℕ)),
            (gs.foldl (orStep N) acc).length = acc.length + gs.length := by
          intro gs
          induction gs with
          | nil => intro acc; simp
          | cons g gs ih =>
            intro acc
            rw [List.foldl_cons, ih]
            have h1 : (orStep N acc g).length = acc.length + 1 := by
              change (acc ++ [_]).length = acc.length + 1
              simp
            rw [h1, List.length_cons]; omega
        have orSets_char : ∀ (gs : List Gate) (i j : ℕ),
            i ∈ (gs.foldl (orStep N) []).getD j [] ↔ j < gs.length ∧
              (i = j ∨ ((gs.getD j ⟨GateOp.or, []⟩).op = GateOp.or ∧
                ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, N ≤ w ∧ w < N + j ∧
                  i ∈ (gs.foldl (orStep N) []).getD (w - N) [])) := by
          intro gs
          induction gs using List.reverseRecOn with
          | nil =>
            intro i j
            simp [List.getD_eq_getElem?_getD]
          | append_singleton gs g ih =>
            intro i j
            rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
            have hlen : (gs.foldl (orStep N) []).length = gs.length := by
              rw [orSets_len]; simp
            have key : ∀ k, k < gs.length →
                (orStep N (gs.foldl (orStep N) []) g).getD k [] =
                  (gs.foldl (orStep N) []).getD k [] := by
              intro k hk
              change ((gs.foldl (orStep N) []) ++ [_]).getD k [] = (gs.foldl (orStep N) []).getD k []
              simp [List.getD_eq_getElem?_getD]
              rw [List.getElem?_append_left (by omega)]
            rcases Nat.lt_trichotomy j gs.length with h | h | h
            · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
                simp [List.getD_eq_getElem?_getD]
                rw [List.getElem?_append_left h]
              rw [key j h, ih i j, e1]
              constructor
              · rintro ⟨_, h3⟩
                refine ⟨by simp; omega, ?_⟩
                rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
                · exact Or.inl h3
                · refine Or.inr ⟨hop, w, hw, h1, h2, ?_⟩
                  rw [key (w - N) (by omega)]
                  exact h3
              · rintro ⟨_, h3⟩
                refine ⟨h, ?_⟩
                rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
                · exact Or.inl h3
                · rw [key (w - N) (by omega)] at h3
                  exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩
            · subst h
              have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
                simp [List.getD_eq_getElem?_getD]
              rw [e1]
              by_cases hop : g.op = GateOp.or
              · have e2 : (orStep N (gs.foldl (orStep N) []) g).getD gs.length [] =
                    gs.length :: (g.inputs.filter (fun w => decide (N ≤ w ∧ w < N + gs.length))).flatMap
                      (fun w => (gs.foldl (orStep N) []).getD (w - N) []) := by
                  simp only [orStep, List.getD_eq_getElem?_getD]
                  rw [List.getElem?_append_right (by omega)]
                  simp [hlen, hop]
                rw [e2]
                simp only [List.mem_cons, List.mem_flatMap, List.mem_filter, decide_eq_true_eq]
                constructor
                · rintro (h3 | ⟨w, ⟨hw, h1, h2⟩, h3⟩)
                  · exact ⟨by simp, Or.inl h3⟩
                  · refine ⟨by simp, Or.inr ⟨hop, w, hw, h1, h2, ?_⟩⟩
                    rw [key (w - N) (by omega)]
                    exact h3
                · rintro ⟨_, h3 | ⟨_, w, hw, h1, h2, h3⟩⟩
                  · exact Or.inl h3
                  · rw [key (w - N) (by omega)] at h3
                    exact Or.inr ⟨w, ⟨hw, h1, h2⟩, h3⟩
              · have e2 : (orStep N (gs.foldl (orStep N) []) g).getD gs.length [] = [gs.length] := by
                  change ((gs.foldl (orStep N) []) ++ [_]).getD gs.length [] = _
                  simp [List.getD_eq_getElem?_getD]
                  rw [List.getElem?_append_right (by omega)]
                  simp [hlen, hop]
                rw [e2]
                simp only [List.mem_singleton]
                constructor
                · intro h3; exact ⟨by simp, Or.inl h3⟩
                · rintro ⟨_, h3 | ⟨hop2, _⟩⟩
                  · exact h3
                  · exact (hop hop2).elim
            · have e0 : (orStep N (gs.foldl (orStep N) []) g).getD j [] = [] := by
                change ((gs.foldl (orStep N) []) ++ [_]).getD j [] = []
                simp [List.getD_eq_getElem?_getD]
                rw [List.getElem?_eq_none (by simp; omega)]
                rfl
              rw [e0]
              constructor
              · intro h0; simp at h0
              · rintro ⟨h0, _⟩; simp at h0; omega
        have orReaches_iff : ∀ k g : ℕ, OrReaches N D (N + k) g ↔ k < D.gates.length ∧
            (g = k ∨ ((gateAt D k).op = GateOp.or ∧ ∃ i ∈ (gateAt D k).inputs,
              i < N + k ∧ OrReaches N D i g)) := by
          intro k g
          have h := orSets_char D.gates g k
          change (N ≤ N + k ∧ g ∈ (D.gates.foldl (orStep N) []).getD (N + k - N) []) ↔ _
          have e : N + k - N = k := by omega
          rw [e, h]
          constructor
          · rintro ⟨_, hk, h3⟩
            refine ⟨hk, ?_⟩
            rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
            · exact Or.inl h3
            · exact Or.inr ⟨hop, w, hw, h2, ⟨h1, h3⟩⟩
          · rintro ⟨hk, h3⟩
            refine ⟨by omega, hk, ?_⟩
            rcases h3 with h3 | ⟨hop, w, hw, h2, h1, h3⟩
            · exact Or.inl h3
            · exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩
        have hOrReaches_self : ∀ k, k < D.gates.length → OrReaches N D (N + k) k := by
          intro k hk
          exact (orReaches_iff k k).mpr ⟨hk, Or.inl rfl⟩
        let OrStepD : ℕ → ℕ → Prop := fun w d =>
          ∃ k < D.gates.length, w = N + k ∧ (gateAt D k).op = GateOp.or ∧
            d ∈ (gateAt D k).inputs ∧ d < N + k
        have reach_orReaches : ∀ {w w2 : ℕ}, Relation.ReflTransGen OrStepD w w2 →
            ∀ g, w2 = N + g → g < D.gates.length → OrReaches N D w g := by
          intro w w2 h
          induction h using Relation.ReflTransGen.head_induction_on with
          | refl =>
            intro g h1 hg; subst h1; exact hOrReaches_self g hg
          | @head a c hstep _ ih =>
            intro g h1 hg
            obtain ⟨k, hk, rfl, hop, hin, hlt⟩ := hstep
            exact (orReaches_iff k g).mpr ⟨hk, Or.inr ⟨hop, c, hin, hlt, ih g h1 hg⟩⟩
        have orReaches_reach : ∀ g w, OrReaches N D w g →
            Relation.ReflTransGen OrStepD w (N + g) ∧ g < D.gates.length := by
          intro g w
          induction w using Nat.strong_induction_on with
          | ind w ih =>
            intro h
            have hnw : N ≤ w := h.1
            obtain ⟨k, rfl⟩ : ∃ k, w = N + k := ⟨w - N, by omega⟩
            obtain ⟨hk, h3⟩ := (orReaches_iff k g).mp h
            rcases h3 with rfl | ⟨hop, i, hi, hlt, hr⟩
            · exact ⟨Relation.ReflTransGen.refl, hk⟩
            · obtain ⟨hr2, hg⟩ := ih i hlt hr
              exact ⟨Relation.ReflTransGen.head ⟨k, hk, rfl, hop, hi, hlt⟩ hr2, hg⟩
        have hOrReaches_step : ∀ w k h, OrReaches N D w k → (gateAt D k).op = GateOp.or →
            ∀ i ∈ (gateAt D k).inputs, i < N + k → OrReaches N D i h → OrReaches N D w h := by
          intro w k h hwk hkop i hi hilt hih
          obtain ⟨r1, _⟩ := orReaches_reach k w hwk
          obtain ⟨r2, hhlen⟩ := orReaches_reach h i hih
          have rstep : OrStepD (N + k) i := ⟨k, (orReaches_reach k w hwk).2, rfl, hkop, hi, hilt⟩
          exact reach_orReaches (r1.trans (Relation.ReflTransGen.head rstep r2)) h rfl hhlen
        have orReaches_le : ∀ w g, OrReaches N D w g → N + g ≤ w := by
          intro w g hreach
          obtain ⟨r, _⟩ := orReaches_reach g w hreach
          suffices hs : ∀ y, Relation.ReflTransGen OrStepD w y → y ≤ w from hs (N + g) r
          intro y hy
          induction hy with
          | refl => exact le_rfl
          | tail _ hstep ih =>
            obtain ⟨k, _, rfl, _, _, hlt⟩ := hstep
            omega
        have orIn_iff_reach : ∀ (p : ℕ) (u : Fin N),
            u ∈ orIn N D p ↔ Relation.ReflTransGen OrStepD p u.val := by
          intro p u
          simp only [orIn, Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · rintro (heq | ⟨k, hk, hreach, hkop, huin⟩)
            · rw [heq]
            · obtain ⟨r1, _⟩ := orReaches_reach k p hreach
              have rstep : OrStepD (N + k) u.val := ⟨k, hk, rfl, hkop, huin, by omega⟩
              exact r1.trans (Relation.ReflTransGen.single rstep)
          · intro h
            suffices hs : ∀ y, Relation.ReflTransGen OrStepD p y →
                y = p ∨ ∃ k < D.gates.length, OrReaches N D p k ∧ (gateAt D k).op = GateOp.or ∧
                  y ∈ (gateAt D k).inputs from hs u.val h
            intro y hy
            induction hy with
            | refl => exact Or.inl rfl
            | tail h1 hstep _ =>
              obtain ⟨k, hk, rfl, hkop, hcin, _⟩ := hstep
              exact Or.inr ⟨k, hk, reach_orReaches h1 k rfl hk, hkop, hcin⟩
        have hOrIn_lt : ∀ w < N, (orIn N D w).card ≤ 1 := by
          intro w hw
          rw [Finset.card_le_one]
          intro a ha b hb
          rw [orIn_iff_reach] at ha hb
          have h1 : ∀ c : Fin N, Relation.ReflTransGen OrStepD w c.val → c.val = w := by
            intro c hc
            rcases Relation.ReflTransGen.cases_head hc with h | ⟨d, hd, _⟩
            · exact h.symm
            · obtain ⟨k, _, h3, _⟩ := hd; omega
          exact Fin.ext ((h1 a ha).trans (h1 b hb).symm)
        have hOrIn_gate : ∀ k u, u ∈ orIn N D (N + k) ↔ k < D.gates.length ∧
            (gateAt D k).op = GateOp.or ∧ ∃ w ∈ (gateAt D k).inputs, w < N + k ∧ u ∈ orIn N D w := by
          intro k u
          rw [orIn_iff_reach]
          constructor
          · intro h
            rcases Relation.ReflTransGen.cases_head h with h | ⟨d, hd, hr⟩
            · have := u.isLt; omega
            · obtain ⟨k', hk', he, hop, hin, hlt⟩ := hd
              have hkk : k' = k := by omega
              subst hkk
              exact ⟨hk', hop, d, hin, hlt, (orIn_iff_reach d u).2 hr⟩
          · rintro ⟨hk, hop, w, hw, hlt, hu⟩
            exact Relation.ReflTransGen.head ⟨k, hk, rfl, hop, hw, hlt⟩ ((orIn_iff_reach w u).1 hu)
        have hOrIn_mono : ∀ w k u, OrReaches N D w k → u ∈ orIn N D (N + k) → u ∈ orIn N D w := by
          intro w k u hreach hu
          rw [orIn_iff_reach] at hu ⊢
          exact (orReaches_reach k w hreach).1.trans hu
        -- Wire evaluation helpers without GateOp.eval / Circuit.wires eq lemmas
        let evalAnd2 (a b : Bool) : Prop := a = true ∧ b = true
        let stepWire (w : List Bool) (g : Gate) : List Bool :=
          w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
        have foldl_length : ∀ (gs : List Gate) (w : List Bool),
            (gs.foldl stepWire w).length = w.length + gs.length := by
          intro gs
          induction gs with
          | nil => intro w; simp
          | cons g gs ih =>
            intro w
            rw [List.foldl_cons, ih]
            simp only [stepWire, List.length_append, List.length_cons, List.length_nil]
            omega
        have foldl_getD_lt : ∀ (gs : List Gate) (w : List Bool) (i : ℕ), i < w.length →
            (gs.foldl stepWire w).getD i false = w.getD i false := by
          intro gs
          induction gs with
          | nil => intro w i _; rfl
          | cons g gs ih =>
            intro w i hi
            rw [List.foldl_cons]
            have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
            rw [ih (stepWire w g) i hlt]
            simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
        have getD_ge : ∀ (w : List Bool) (i : ℕ), w.length ≤ i → w.getD i false = false := by
          intro w i hi
          simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]
        have foldl_getD_gate : ∀ (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length),
            (gs.foldl stepWire w).getD (w.length + j) false =
              (gs[j]'hj).op.eval ((gs[j]'hj).inputs.map fun i =>
                if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
          intro gs
          induction gs with
          | nil => intro w j hj; simp at hj
          | cons g gs ih =>
            intro w j hj
            rw [List.foldl_cons]
            cases j with
            | zero =>
              have h1 : w.length < (stepWire w g).length := by simp [stepWire]
              rw [Nat.add_zero, foldl_getD_lt gs (stepWire w g) w.length h1]
              simp only [List.getElem_cons_zero]
              have h2 : (stepWire w g).getD w.length false =
                  g.op.eval (g.inputs.map fun i => w.getD i false) := by
                simp [stepWire, List.getD_eq_getElem?_getD]
              rw [h2]
              congr 1
              apply List.map_congr_left
              intro i _
              by_cases hi : i < w.length
              · rw [if_pos hi, foldl_getD_lt gs (stepWire w g) i (by simp [stepWire]; omega)]
                simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
              · rw [if_neg hi]; exact getD_ge w i (by omega)
            | succ j =>
              have hj' : j < gs.length := by simpa using hj
              have key := ih (stepWire w g) j hj'
              have hl : (stepWire w g).length = w.length + 1 := by simp [stepWire]
              rw [hl] at key
              have e : w.length + (j + 1) = w.length + 1 + j := by omega
              simp only [List.getElem_cons_succ]
              rw [e]
              exact key
        let wireVal (w : ℕ) (x : Fin N → Bool) : Bool :=
          (D.gates.foldl stepWire (List.ofFn x)).getD w false
        have wireVal_lt : ∀ (i : Fin N) (x : Fin N → Bool), wireVal i.val x = x i := by
          intro i x
          change (D.gates.foldl stepWire (List.ofFn x)).getD i.val false = x i
          rw [foldl_getD_lt D.gates (List.ofFn x) i.val (by simp)]
          simp [List.getD_eq_getElem?_getD]
        have wireVal_gate : ∀ (j : ℕ) (hj : j < D.gates.length) (x : Fin N → Bool),
            wireVal (N + j) x = (gateAt D j).op.eval
              [wireVal (opnd D j 0) x, wireVal (opnd D j 1) x] := by
          intro j hj x
          change (D.gates.foldl stepWire (List.ofFn x)).getD (N + j) false = _
          have hlen_ofFn : (List.ofFn x).length = N := by simp
          have h1 := foldl_getD_gate D.gates (List.ofFn x) j hj
          rw [hlen_ofFn] at h1
          rw [h1]
          have hgat : gateAt D j = D.gates[j]'hj := by
            unfold gateAt; simp [List.getD_eq_getElem?_getD, hj]
          rw [hgat]
          have hlen2 : (D.gates[j]'hj).inputs.length = 2 := hDAO.2.2 _ (List.getElem_mem hj)
          have hinputs : (D.gates[j]'hj).inputs = [opnd D j 0, opnd D j 1] := by
            unfold opnd
            rw [hgat]
            rcases hlist : (D.gates[j]'hj).inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, cs⟩⟩⟩
            · simp [hlist] at hlen2
            · simp [hlist] at hlen2
            · simp [List.getD_eq_getElem?_getD]
            · simp [hlist] at hlen2
          rw [hinputs]
          simp only [List.map_cons, List.map_nil]
          have hlt0 : opnd D j 0 < N + j := hDAO.2.1 j hj (opnd D j 0) (by
            rw [hgat, hinputs]; simp)
          have hlt1 : opnd D j 1 < N + j := hDAO.2.1 j hj (opnd D j 1) (by
            rw [hgat, hinputs]; simp)
          rw [if_pos hlt0, if_pos hlt1]
        have wireVal_gate_and : ∀ (j : ℕ), j < D.gates.length → (gateAt D j).op = GateOp.and →
            ∀ x, wireVal (N + j) x = true ↔
              wireVal (opnd D j 0) x = true ∧ wireVal (opnd D j 1) x = true := by
          intro j hj hop x
          rw [wireVal_gate j hj x, hop]
          have hev : ∀ a b : Bool, GateOp.and.eval [a, b] = (a && b) := by
            intro a b; cases a <;> cases b <;> rfl
          rw [hev, Bool.and_eq_true]
        have wireVal_gate_or : ∀ (j : ℕ), j < D.gates.length → (gateAt D j).op = GateOp.or →
            ∀ x, wireVal (N + j) x = true ↔
              wireVal (opnd D j 0) x = true ∨ wireVal (opnd D j 1) x = true := by
          intro j hj hop x
          rw [wireVal_gate j hj x, hop]
          have hev : ∀ a b : Bool, GateOp.or.eval [a, b] = (a || b) := by
            intro a b; cases a <;> cases b <;> rfl
          rw [hev, Bool.or_eq_true]
        have wireVal_ge : ∀ (j : ℕ), D.gates.length ≤ j → ∀ x, wireVal (N + j) x = false := by
          intro j hj x
          change (D.gates.foldl stepWire (List.ofFn x)).getD (N + j) false = false
          apply getD_ge
          rw [foldl_length, List.length_ofFn]
          omega
        have gateVal_eq_wireVal : ∀ (j : ℕ) (x : Fin N → Bool),
            PEqualNP.EdgeOwnership.gateVal N D j x = wireVal (N + j) x := by
          intro j x; rfl
        have wireVal_orIn : ∀ (w : ℕ) (u : Fin N) (x : Fin N → Bool),
            u ∈ orIn N D w → x u = true → wireVal w x = true := by
          intro w u x hu hxu
          rw [orIn_iff_reach] at hu
          induction hu using Relation.ReflTransGen.head_induction_on with
          | refl => rw [wireVal_lt u x]; exact hxu
          | @head a c hstep _ ih =>
            obtain ⟨k, hk, rfl, hkop, hcin, _⟩ := hstep
            rw [wireVal_gate_or k hk hkop x]
            have hlen2 : (gateAt D k).inputs.length = 2 := by
              apply hDAO.2.2; unfold gateAt; simp [List.getD_eq_getElem?_getD, hk]
            obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hcin
            have hi2 : i < 2 := by omega
            have hceq : (gateAt D k).inputs[i] = opnd D k ⟨i, hi2⟩ := by
              unfold opnd; simp [List.getD_eq_getElem?_getD, hi]
            rw [hceq] at ih
            have hi01 : i = 0 ∨ i = 1 := by omega
            rcases hi01 with rfl | rfl
            · exact Or.inl ih
            · exact Or.inr ih
        have wireVal_orIn_iff_no_and : ∀ (w : ℕ) (x : Fin N → Bool),
            (¬ ∃ g < D.gates.length, (gateAt D g).op = GateOp.and ∧ OrReaches N D w g) →
            (wireVal w x = true ↔ ∃ u ∈ orIn N D w, x u = true) := by
          intro w
          induction w using Nat.strong_induction_on with
          | ind w ih =>
            intro x hnoAnd
            constructor
            · intro hval
              by_cases hwN : w < N
              · refine ⟨⟨w, hwN⟩, ?_, ?_⟩
                · simp only [orIn, Finset.mem_filter, Finset.mem_univ, true_and]
                  exact Or.inl True.intro
                · rw [← wireVal_lt ⟨w, hwN⟩ x]; exact hval
              · obtain ⟨j, rfl⟩ : ∃ j, w = N + j := ⟨w - N, by omega⟩
                by_cases hjlen : j < D.gates.length
                · have hjop : (gateAt D j).op = GateOp.or := by
                    by_contra hne
                    have hand : (gateAt D j).op = GateOp.and := by
                      have hmem := hDAO.1 (gateAt D j) (by
                        unfold gateAt; simp [List.getD_eq_getElem?_getD, hjlen, List.getElem_mem])
                      rcases hmem with h | h
                      · exact h
                      · exact absurd h hne
                    exact hnoAnd ⟨j, hjlen, hand, hOrReaches_self j hjlen⟩
                  rw [wireVal_gate_or j hjlen hjop x] at hval
                  have hlen2 : (gateAt D j).inputs.length = 2 := by
                    apply hDAO.2.2; unfold gateAt; simp [List.getD_eq_getElem?_getD, hjlen]
                  have hsub_reach : ∀ b : Fin 2, ¬ ∃ g < D.gates.length,
                      (gateAt D g).op = GateOp.and ∧ OrReaches N D (opnd D j b) g := by
                    intro b ⟨g, hglen, hgop, hreach⟩
                    have hmem_in : opnd D j b ∈ (gateAt D j).inputs := by
                      unfold opnd; simp [List.getD_eq_getElem?_getD]
                      have hb : (b : ℕ) < (gateAt D j).inputs.length := by omega
                      simp [hb, List.getElem_mem]
                    have hlt : opnd D j b < N + j := hDAO.2.1 j hjlen (opnd D j b) hmem_in
                    exact hnoAnd ⟨g, hglen, hgop, hOrReaches_step (N + j) j g
                      (hOrReaches_self j hjlen) hjop (opnd D j b) hmem_in hlt hreach⟩
                  rcases hval with h0 | h1
                  · have hmem_in : opnd D j 0 ∈ (gateAt D j).inputs := by
                      unfold opnd; simp [List.getD_eq_getElem?_getD]
                      have hb : (0 : ℕ) < (gateAt D j).inputs.length := by omega
                      simp [hb, List.getElem_mem]
                    have hlt : opnd D j 0 < N + j := hDAO.2.1 j hjlen (opnd D j 0) hmem_in
                    obtain ⟨u, hu, hxu⟩ := (ih (opnd D j 0) hlt x (hsub_reach 0)).mp h0
                    refine ⟨u, ?_, hxu⟩
                    rw [hOrIn_gate]
                    exact ⟨hjlen, hjop, opnd D j 0, hmem_in, hlt, hu⟩
                  · have hmem_in : opnd D j 1 ∈ (gateAt D j).inputs := by
                      unfold opnd; simp [List.getD_eq_getElem?_getD]
                      have hb : (1 : ℕ) < (gateAt D j).inputs.length := by omega
                      simp [hb, List.getElem_mem]
                    have hlt : opnd D j 1 < N + j := hDAO.2.1 j hjlen (opnd D j 1) hmem_in
                    obtain ⟨u, hu, hxu⟩ := (ih (opnd D j 1) hlt x (hsub_reach 1)).mp h1
                    refine ⟨u, ?_, hxu⟩
                    rw [hOrIn_gate]
                    exact ⟨hjlen, hjop, opnd D j 1, hmem_in, hlt, hu⟩
                · rw [wireVal_ge j (by omega) x] at hval
                  cases hval
            · rintro ⟨u, hu, hxu⟩
              exact wireVal_orIn w u x hu hxu
        have hSingle_false : ∀ (u : Fin N), graphFun G ∅ (fun i => decide (i = u)) = false := by
          intro u
          by_contra hne
          have ht : graphFun G ∅ (fun i => decide (i = u)) = true := Bool.eq_true_of_not_eq_false hne
          unfold graphFun at ht
          simp only [Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or,
            decide_eq_true_eq] at ht
          rcases ht with ⟨a, b, hadj, ha, hb⟩
          subst ha; subst hb
          exact G.loopless.irrefl _ hadj
        have hOrIn_not_belowF : ∀ k u, u ∈ orIn N D (N + k) → ¬ BelowF G D k := by
          intro k u hu hbel
          have hval : gateVal N D k (fun i => decide (i = u)) = true := by
            rw [gateVal_eq_wireVal]
            exact wireVal_orIn (N + k) u (fun i => decide (i = u)) hu (by simp)
          have hf := hbel (fun i => decide (i = u)) hval
          rw [hSingle_false u] at hf
          cases hf
        have hTop_adj : ∀ a ∈ tops G D, ∀ u ∈ PEqualNP.TopForm.side D a 0,
            ∀ v ∈ PEqualNP.TopForm.side D a 1, G.Adj u v ∧ s(u, v) ∈ starEdges G D := by
          intro a ha u hu v hv
          have ha' := ha
          simp only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range] at ha'
          rcases ha' with ⟨halen, haop, habel⟩
          have hval : gateVal N D a (pairInput u v) = true := by
            rw [gateVal_eq_wireVal, wireVal_gate_and a halen haop]
            exact ⟨wireVal_orIn (opnd D a 0) u (pairInput u v) hu (by simp [pairInput]),
              wireVal_orIn (opnd D a 1) v (pairInput u v) hv (by simp [pairInput])⟩
          have hf := habel (pairInput u v) hval
          unfold graphFun at hf
          simp only [Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or,
            decide_eq_true_eq] at hf
          rcases hf with ⟨p, q, hadj, hp, hq⟩
          have hp' : p = u ∨ p = v := by simpa [pairInput] using hp
          have hq' : q = u ∨ q = v := by simpa [pairInput] using hq
          have huv_adj : G.Adj u v := by
            rcases hp' with rfl | rfl <;> rcases hq' with rfl | rfl
            · exact absurd hadj (G.loopless.irrefl _)
            · exact hadj
            · exact hadj.symm
            · exact absurd hadj (G.loopless.irrefl _)
          refine ⟨huv_adj, ?_⟩
          simp only [starEdges, Finset.mem_biUnion, Finset.mem_image, Finset.mem_product]
          exact ⟨a, ha, (u, v), ⟨hu, hv⟩, rfl⟩
        have hTop_no_self : ∀ a ∈ tops G D, ∀ u : Fin N,
            ¬ (u ∈ PEqualNP.TopForm.side D a 0 ∧ u ∈ PEqualNP.TopForm.side D a 1) := by
          intro a ha u ⟨hu0, hu1⟩
          exact G.loopless.irrefl u (hTop_adj a ha u hu0 u hu1).1
        have hAnd_split : ∀ g < D.gates.length, (gateAt D g).op = GateOp.and →
            g ∈ tops G D ∨ g ∈ junk G D := by
          intro g hglen hgop
          by_cases hbel : BelowF G D g
          · left; simp only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range]; exact ⟨hglen, hgop, hbel⟩
          · right
            change g ∈ (Finset.range D.gates.length).filter (fun j => IsDirtyAnd N G D j)
            rw [Finset.mem_filter, Finset.mem_range]
            refine ⟨hglen, ?_⟩
            change (gateAt D g).op = GateOp.and ∧ g < D.gates.length ∧
              ∃ x, gateVal N D g x = true ∧ graphFun G ∅ x = false
            refine ⟨hgop, hglen, ?_⟩
            by_contra! hnone
            apply hbel
            intro x hx
            by_contra hfx
            have hfx' : graphFun G ∅ x = false := Bool.eq_false_iff.mpr hfx
            exact hnone x hx hfx'
        have cones_len : ∀ (gs : List Gate) (acc : List (List ℕ)),
            (gs.foldl (coneStep N) acc).length = acc.length + gs.length := by
          intro gs
          induction gs with
          | nil => intro acc; simp
          | cons gc gs ih =>
            intro acc
            rw [List.foldl_cons, ih]
            have h1 : (coneStep N acc gc).length = acc.length + 1 := by
              change (acc ++ [_]).length = acc.length + 1; simp
            rw [h1, List.length_cons]; omega
        have cones_char : ∀ (gs : List Gate) (i j : ℕ),
            i ∈ (gs.foldl (coneStep N) []).getD j [] ↔ j < gs.length ∧
              ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, N ≤ w ∧ w < N + j ∧
                (i = w - N ∨ i ∈ (gs.foldl (coneStep N) []).getD (w - N) []) := by
          intro gs
          induction gs using List.reverseRecOn with
          | nil => intro i j; simp [List.getD_eq_getElem?_getD]
          | append_singleton gs gc ih =>
            intro i j
            rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
            have hlen : (gs.foldl (coneStep N) []).length = gs.length := by
              rw [cones_len]; simp
            have key : ∀ k, k < gs.length →
                (coneStep N (gs.foldl (coneStep N) []) gc).getD k [] =
                  (gs.foldl (coneStep N) []).getD k [] := by
              intro k hk
              simp only [coneStep, List.getD_eq_getElem?_getD]
              rw [List.getElem?_append_left (by omega)]
            rcases Nat.lt_trichotomy j gs.length with h | h | h
            · have e1 : (gs ++ [gc]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
                simp [List.getD_eq_getElem?_getD]; rw [List.getElem?_append_left h]
              rw [key j h, ih i j, e1]
              constructor
              · rintro ⟨_, w, hw, h1, h2, h3⟩
                refine ⟨by simp; omega, w, hw, h1, h2, ?_⟩
                rcases h3 with rfl | h3
                · exact Or.inl rfl
                · right; rw [key (w - N) (by omega)]; exact h3
              · rintro ⟨_, w, hw, h1, h2, h3⟩
                refine ⟨h, w, hw, h1, h2, ?_⟩
                rcases h3 with rfl | h3
                · exact Or.inl rfl
                · right; rw [key (w - N) (by omega)] at h3; exact h3
            · subst h
              have e1 : (gs ++ [gc]).getD gs.length ⟨GateOp.or, []⟩ = gc := by
                simp [List.getD_eq_getElem?_getD]
              rw [e1]
              have e2 : (coneStep N (gs.foldl (coneStep N) []) gc).getD gs.length [] =
                  (gc.inputs.filter (fun w => decide (N ≤ w ∧ w < N + gs.length))).flatMap
                    (fun w => (w - N) :: (gs.foldl (coneStep N) []).getD (w - N) []) := by
                simp only [coneStep, List.getD_eq_getElem?_getD]
                rw [List.getElem?_append_right (by omega)]
                simp [hlen]
              rw [e2]
              simp only [List.mem_flatMap, List.mem_filter, decide_eq_true_eq, List.mem_cons]
              constructor
              · rintro ⟨w, ⟨hw, h1, h2⟩, h3⟩
                refine ⟨by simp, w, hw, h1, h2, ?_⟩
                rcases h3 with rfl | h3
                · exact Or.inl rfl
                · right; rw [key (w - N) (by omega)]; exact h3
              · rintro ⟨_, w, hw, h1, h2, h3⟩
                refine ⟨w, ⟨hw, h1, h2⟩, ?_⟩
                rcases h3 with rfl | h3
                · exact Or.inl rfl
                · right; rw [key (w - N) (by omega)] at h3; exact h3
            · have e0 : (coneStep N (gs.foldl (coneStep N) []) gc).getD j [] = [] := by
                simp only [coneStep, List.getD_eq_getElem?_getD]
                rw [List.getElem?_eq_none (by simp; omega)]; rfl
              rw [e0]
              constructor
              · intro h0; simp at h0
              · rintro ⟨h0, _⟩; simp at h0; omega
        have inCone_iff : ∀ i j : ℕ, InCone N D i j ↔ j < D.gates.length ∧
            ∃ w ∈ (gateAt D j).inputs, N ≤ w ∧ w < N + j ∧
              (i = w - N ∨ InCone N D i (w - N)) := by
          intro i j; exact cones_char D.gates i j
        have orReaches_inCone : ∀ k0 g0, OrReaches N D (N + k0) g0 → g0 = k0 ∨ InCone N D g0 k0 := by
          intro k0 g0 hreach0
          obtain ⟨r0, hg0len⟩ := orReaches_reach g0 (N + k0) hreach0
          suffices hs : ∀ w, Relation.ReflTransGen OrStepD w (N + g0) →
              ∀ k, w = N + k → g0 = k ∨ InCone N D g0 k from hs (N + k0) r0 k0 rfl
          intro w hw
          induction hw using Relation.ReflTransGen.head_induction_on with
          | refl => intro k hk; left; omega
          | @head x y hstep hrest ih =>
            intro k hk
            obtain ⟨k', hk', rfl, _, hyin, hylt⟩ := hstep
            have hkk' : k' = k := by omega
            subst hkk'
            by_cases hyN : N ≤ y
            · obtain ⟨k2, rfl⟩ : ∃ k2, y = N + k2 := ⟨y - N, by omega⟩
              right
              rw [inCone_iff]
              refine ⟨hk', N + k2, hyin, hyN, hylt, ?_⟩
              have e : N + k2 - N = k2 := by omega
              rw [e]
              exact ih k2 rfl
            · exfalso
              have := (reach_orReaches hrest g0 rfl hg0len).1
              omega
        have hTop_not_in_cone : ∀ a ∈ tops G D, ∀ b : Fin 2, ∀ g,
            OrReaches N D (opnd D a b) g → g ∉ tops G D := by
          intro a ha b g hreach hg
          simp only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range] at ha hg
          rcases ha with ⟨halen, haop, _⟩
          rcases hg with ⟨hglen, hgop, hgbel⟩
          have hlen2 : (gateAt D a).inputs.length = 2 := by
            apply hDAO.2.2; unfold gateAt; simp [List.getD_eq_getElem?_getD, halen]
          have hmem_in : opnd D a b ∈ (gateAt D a).inputs := by
            unfold opnd; simp [List.getD_eq_getElem?_getD]
            have hb : (b : ℕ) < (gateAt D a).inputs.length := by omega
            simp [hb, List.getElem_mem]
          have hlt : opnd D a b < N + a := hDAO.2.1 a halen (opnd D a b) hmem_in
          have hincone : InCone N D g a := by
            have hnw : N ≤ opnd D a b := hreach.1
            obtain ⟨k0, hk0eq⟩ : ∃ k0, opnd D a b = N + k0 := ⟨opnd D a b - N, by omega⟩
            rw [hk0eq] at hreach hmem_in hlt hnw
            rw [inCone_iff]
            refine ⟨halen, N + k0, hmem_in, hnw, hlt, ?_⟩
            have e : N + k0 - N = k0 := by omega
            rw [e]
            exact orReaches_inCone k0 g hreach
          exact hDtop g hglen a halen hgop hgbel haop hincone
        have hWire_witness : ∀ (w : ℕ) (u v : Fin N),
            wireVal w (pairInput u v) = true →
            (u ∈ orIn N D w ∨ v ∈ orIn N D w) ∨
              ∃ g < D.gates.length, (gateAt D g).op = GateOp.and ∧ OrReaches N D w g ∧
                wireVal (N + g) (pairInput u v) = true := by
          intro w u v
          induction w using Nat.strong_induction_on with
          | ind w ih =>
            intro hval
            by_cases hwN : w < N
            · left
              change wireVal (⟨w, hwN⟩ : Fin N).val (pairInput u v) = true at hval
              rw [wireVal_lt ⟨w, hwN⟩ (pairInput u v)] at hval
              have hmem : ⟨w, hwN⟩ = u ∨ ⟨w, hwN⟩ = v := by simpa [pairInput] using hval
              rcases hmem with rfl | rfl
              · left; simp only [orIn, Finset.mem_filter, Finset.mem_univ, true_and]; exact Or.inl True.intro
              · right; simp only [orIn, Finset.mem_filter, Finset.mem_univ, true_and]; exact Or.inl True.intro
            · obtain ⟨j, rfl⟩ : ∃ j, w = N + j := ⟨w - N, by omega⟩
              by_cases hjlen : j < D.gates.length
              · have hmem := hDAO.1 (gateAt D j) (by
                  unfold gateAt; simp [List.getD_eq_getElem?_getD, hjlen, List.getElem_mem])
                rcases hmem with hjop | hjop
                · right; exact ⟨j, hjlen, hjop, hOrReaches_self j hjlen, hval⟩
                · rw [wireVal_gate_or j hjlen hjop (pairInput u v)] at hval
                  have hlen2 : (gateAt D j).inputs.length = 2 := by
                    apply hDAO.2.2; unfold gateAt; simp [List.getD_eq_getElem?_getD, hjlen]
                  have hstep_b : ∀ b : Fin 2, wireVal (opnd D j b) (pairInput u v) = true →
                      (u ∈ orIn N D (N + j) ∨ v ∈ orIn N D (N + j)) ∨
                        ∃ g < D.gates.length, (gateAt D g).op = GateOp.and ∧ OrReaches N D (N + j) g ∧
                          wireVal (N + g) (pairInput u v) = true := by
                    intro b hbval
                    have hmem_in : opnd D j b ∈ (gateAt D j).inputs := by
                      unfold opnd; simp [List.getD_eq_getElem?_getD]
                      have hb : (b : ℕ) < (gateAt D j).inputs.length := by omega
                      simp [hb, List.getElem_mem]
                    have hlt : opnd D j b < N + j := hDAO.2.1 j hjlen (opnd D j b) hmem_in
                    rcases ih (opnd D j b) hlt hbval with (hu | hv) | ⟨g, hglen, hgop, hreach, hgval⟩
                    · left; left; rw [hOrIn_gate]; exact ⟨hjlen, hjop, opnd D j b, hmem_in, hlt, hu⟩
                    · left; right; rw [hOrIn_gate]; exact ⟨hjlen, hjop, opnd D j b, hmem_in, hlt, hv⟩
                    · right; exact ⟨g, hglen, hgop,
                        hOrReaches_step (N + j) j g (hOrReaches_self j hjlen) hjop (opnd D j b) hmem_in hlt hreach,
                        hgval⟩
                  rcases hval with h0 | h1
                  · exact hstep_b 0 h0
                  · exact hstep_b 1 h1
              · rw [wireVal_ge j (by omega) (pairInput u v)] at hval; cases hval
        have hTop_witness : ∀ e ∈ Ustar G D, ∃ a ∈ tops G D, ∃ u v : Fin N,
            e = s(u, v) ∧ u ≠ v ∧ wireVal (N + a) (pairInput u v) = true := by
          intro e heU
          have heG : e ∈ G.edgeFinset := (Finset.mem_sdiff.mp heU).1
          rw [edgeFinset_eq, Finset.mem_image] at heG
          obtain ⟨d, hdE, rfl⟩ := heG
          let u := L d.1
          let v := R d.2
          have huv : u ≠ v := hcross d.1 d.2
          have hadj : G.Adj u v := (incidence d.1 d.2).mpr hdE
          have hfx : graphFun G ∅ (pairInput u v) = true := by
            unfold graphFun
            simp only [Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or,
              decide_eq_true_eq]
            exact ⟨u, v, hadj, by simp [pairInput], by simp [pairInput]⟩
          have hDout : wireVal D.output (pairInput u v) = true := by
            have h1 := congrFun hDeval (pairInput u v)
            change wireVal D.output (pairInput u v) = graphFun G ∅ (pairInput u v) at h1
            rw [h1]; exact hfx
          have hDout_bel : ∀ y : Fin N → Bool, wireVal D.output y = true → graphFun G ∅ y = true := by
            intro y hy
            have h1 := congrFun hDeval y
            change wireVal D.output y = graphFun G ∅ y at h1
            rw [← h1]; exact hy
          suffices htrace : ∀ w, wireVal w (pairInput u v) = true →
              (∀ y, wireVal w y = true → graphFun G ∅ y = true) →
              ∃ a ∈ tops G D, wireVal (N + a) (pairInput u v) = true by
            obtain ⟨a, ha, haval⟩ := htrace D.output hDout hDout_bel
            exact ⟨a, ha, u, v, rfl, huv, haval⟩
          intro w
          induction w using Nat.strong_induction_on with
          | ind w ih =>
            intro hwval hwbel
            by_cases hwN : w < N
            · exfalso
              have hval1 : wireVal w (fun i => decide (i = ⟨w, hwN⟩)) = true := by
                change wireVal (⟨w, hwN⟩ : Fin N).val (fun i => decide (i = ⟨w, hwN⟩)) = true
                rw [wireVal_lt]; simp
              have hf := hwbel _ hval1
              rw [hSingle_false ⟨w, hwN⟩] at hf
              cases hf
            · obtain ⟨j, rfl⟩ : ∃ j, w = N + j := ⟨w - N, by omega⟩
              by_cases hjlen : j < D.gates.length
              · have hmem := hDAO.1 (gateAt D j) (by
                  unfold gateAt; simp [List.getD_eq_getElem?_getD, hjlen, List.getElem_mem])
                rcases hmem with hjop | hjop
                · refine ⟨j, ?_, hwval⟩
                  simp only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range]
                  exact ⟨hjlen, hjop, hwbel⟩
                · rw [wireVal_gate_or j hjlen hjop (pairInput u v)] at hwval
                  have hlen2 : (gateAt D j).inputs.length = 2 := by
                    apply hDAO.2.2; unfold gateAt; simp [List.getD_eq_getElem?_getD, hjlen]
                  have hsub_bel : ∀ b : Fin 2, ∀ y, wireVal (opnd D j b) y = true →
                      graphFun G ∅ y = true := by
                    intro b y hy
                    apply hwbel y
                    rw [wireVal_gate_or j hjlen hjop y]
                    fin_cases b
                    · exact Or.inl hy
                    · exact Or.inr hy
                  rcases hwval with h0 | h1
                  · have hmem_in : opnd D j 0 ∈ (gateAt D j).inputs := by
                      unfold opnd; simp [List.getD_eq_getElem?_getD]
                      have hb : (0 : ℕ) < (gateAt D j).inputs.length := by omega
                      simp [hb, List.getElem_mem]
                    exact ih (opnd D j 0) (hDAO.2.1 j hjlen (opnd D j 0) hmem_in) h0 (hsub_bel 0)
                  · have hmem_in : opnd D j 1 ∈ (gateAt D j).inputs := by
                      unfold opnd; simp [List.getD_eq_getElem?_getD]
                      have hb : (1 : ℕ) < (gateAt D j).inputs.length := by omega
                      simp [hb, List.getElem_mem]
                    exact ih (opnd D j 1) (hDAO.2.1 j hjlen (opnd D j 1) hmem_in) h1 (hsub_bel 1)
              · rw [wireVal_ge j (by omega) (pairInput u v)] at hwval; cases hwval
        have hU_witness : ∀ e ∈ Ustar G D, ∃ a ∈ tops G D, ∃ u v : Fin N, e = s(u, v) ∧ u ≠ v ∧
            ∀ b : Fin 2, (u ∈ PEqualNP.TopForm.side D a b ∨ v ∈ PEqualNP.TopForm.side D a b) ∨
              ∃ g < D.gates.length, (gateAt D g).op = GateOp.and ∧
                OrReaches N D (opnd D a b) g ∧ wireVal (N + g) (pairInput u v) = true := by
          intro e heU
          obtain ⟨a, ha, u, v, rfl, huv, haval⟩ := hTop_witness e heU
          have ha' := ha
          simp only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range] at ha'
          rw [wireVal_gate_and a ha'.1 ha'.2.1 (pairInput u v)] at haval
          refine ⟨a, ha, u, v, rfl, huv, fun b => ?_⟩
          fin_cases b
          · exact hWire_witness (opnd D a 0) u v haval.1
          · exact hWire_witness (opnd D a 1) u v haval.2
        by_cases hj0 : (junk G D).card = 0
        · exfalso
          have hJunkEmpty : junk G D = ∅ := Finset.card_eq_zero.mp hj0
          obtain ⟨e, heU⟩ := hU
          obtain ⟨a, ha, u, v, rfl, huv, hside⟩ := hU_witness e heU
          have hnoAnd : ∀ b : Fin 2, ¬ ∃ g < D.gates.length, (gateAt D g).op = GateOp.and ∧
              OrReaches N D (opnd D a b) g ∧ wireVal (N + g) (pairInput u v) = true := by
            intro b ⟨g, hglen, hgop, hreach, _⟩
            rcases hAnd_split g hglen hgop with htop | hjunk
            · exact hTop_not_in_cone a ha b g hreach htop
            · rw [hJunkEmpty] at hjunk; exact absurd hjunk (Finset.notMem_empty _)
          have h0 := (hside 0).resolve_right (hnoAnd 0)
          have h1 := (hside 1).resolve_right (hnoAnd 1)
          have hstar : s(u, v) ∈ starEdges G D := by
            simp only [starEdges, Finset.mem_biUnion, Finset.mem_image, Finset.mem_product]
            rcases h0 with hu0 | hv0 <;> rcases h1 with hu1 | hv1
            · exact absurd ⟨hu0, hu1⟩ (hTop_no_self a ha u)
            · exact ⟨a, ha, (u, v), ⟨hu0, hv1⟩, rfl⟩
            · exact ⟨a, ha, (v, u), ⟨hv0, hu1⟩, Sym2.eq_swap⟩
            · exact absurd ⟨hv0, hv1⟩ (hTop_no_self a ha v)
          exact (Finset.mem_sdiff.mp heU).2 hstar
        · have hj1 : (junk G D).card = 1 := by omega
          obtain ⟨g, hg_eq⟩ := Finset.card_eq_one.mp hj1
          have hg_mem : g ∈ junk G D := by rw [hg_eq]; exact Finset.mem_singleton_self g
          have hg_mem' := hg_mem
          change g ∈ (Finset.range D.gates.length).filter (fun j => IsDirtyAnd N G D j) at hg_mem'
          rw [Finset.mem_filter, Finset.mem_range] at hg_mem'
          have hg_len : g < D.gates.length := hg_mem'.1
          have hg_op : (gateAt D g).op = GateOp.and := hg_mem'.2.1
          have hg_nbel : ¬ BelowF G D g := by
            intro hbel
            obtain ⟨x, hx1, hx2⟩ := hg_mem'.2.2.2
            have := hbel x hx1
            rw [this] at hx2
            cases hx2
          have hNoAnd_g : ∀ b : Fin 2, ¬ ∃ g' < D.gates.length, (gateAt D g').op = GateOp.and ∧
              OrReaches N D (opnd D g b) g' := by
            intro b ⟨g', hg'len, hg'op, hreach⟩
            rcases hAnd_split g' hg'len hg'op with htop | hjunk
            · have hlen2 : (gateAt D g).inputs.length = 2 := by
                apply hDAO.2.2; unfold gateAt; simp [List.getD_eq_getElem?_getD, hg_len]
              have hmem_in : opnd D g b ∈ (gateAt D g).inputs := by
                unfold opnd; simp [List.getD_eq_getElem?_getD]
                have hb : (b : ℕ) < (gateAt D g).inputs.length := by omega
                simp [hb, List.getElem_mem]
              have hlt : opnd D g b < N + g := hDAO.2.1 g hg_len (opnd D g b) hmem_in
              have hnw : N ≤ opnd D g b := hreach.1
              obtain ⟨k0, hk0eq⟩ : ∃ k0, opnd D g b = N + k0 := ⟨opnd D g b - N, by omega⟩
              rw [hk0eq] at hreach hmem_in hlt hnw
              have hincone : InCone N D g' g := by
                rw [inCone_iff]
                refine ⟨hg_len, N + k0, hmem_in, hnw, hlt, ?_⟩
                have e : N + k0 - N = k0 := by omega
                rw [e]
                exact orReaches_inCone k0 g' hreach
              have htop' := htop
              simp only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range] at htop'
              exact hDtop g' hg'len g hg_len hg'op htop'.2.2 hg_op hincone
            · rw [hg_eq, Finset.mem_singleton] at hjunk
              subst hjunk
              have hlen2 : (gateAt D g').inputs.length = 2 := by
                apply hDAO.2.2; unfold gateAt; simp [List.getD_eq_getElem?_getD, hg_len]
              have hmem_in : opnd D g' b ∈ (gateAt D g').inputs := by
                unfold opnd; simp [List.getD_eq_getElem?_getD]
                have hb : (b : ℕ) < (gateAt D g').inputs.length := by omega
                simp [hb, List.getElem_mem]
              have hlt : opnd D g' b < N + g' := hDAO.2.1 g' hg_len (opnd D g' b) hmem_in
              have hnw : N + g' ≤ opnd D g' b := orReaches_le (opnd D g' b) g' hreach
              omega
          let S0 : Finset (Fin N) := orIn N D (opnd D g 0)
          let S1 : Finset (Fin N) := orIn N D (opnd D g 1)
          have hg_iff : ∀ x : Fin N → Bool, wireVal (N + g) x = true ↔
              (∃ u ∈ S0, x u = true) ∧ (∃ v ∈ S1, x v = true) := by
            intro x
            rw [wireVal_gate_and g hg_len hg_op x,
              wireVal_orIn_iff_no_and (opnd D g 0) x (hNoAnd_g 0),
              wireVal_orIn_iff_no_and (opnd D g 1) x (hNoAnd_g 1)]
          -- Generalized Marked Leaves Lemma
          have hGML : ∀ (W : Finset ℕ) (S : Finset (Fin N)),
              S ⊆ W.biUnion (fun w => orIn N D w) →
              (∀ h ∈ lam G D, (S ∩ orIn N D (N + h)).card ≤ 1) →
              S.card ≤ W.card + ((orN G D \ lam G D).filter fun h =>
                (∃ w ∈ W, OrReaches N D w h) ∧ 2 ≤ (S ∩ orIn N D (N + h)).card).card := by
            intro W S hSub hLam
            let B : Finset (Fin N) → Finset ℕ := fun T =>
              (orN G D \ lam G D).filter fun h =>
                (∃ w ∈ W, OrReaches N D w h) ∧ 2 ≤ (T ∩ orIn N D (N + h)).card
            have hB_sub : ∀ T₁ T₂ : Finset (Fin N), T₁ ⊆ T₂ → B T₁ ⊆ B T₂ := by
              intro T₁ T₂ h12 h hh
              simp only [B, Finset.mem_filter] at hh ⊢
              refine ⟨hh.1, hh.2.1, le_trans hh.2.2 (Finset.card_le_card (Finset.inter_subset_inter_right h12))⟩
            have h_in_B : ∀ T : Finset (Fin N), T ⊆ S → ∀ w,
                (∃ w0 ∈ W, w = w0 ∨ ∃ k0, OrReaches N D w0 k0 ∧ (gateAt D k0).op = GateOp.or ∧
                  w ∈ (gateAt D k0).inputs ∧ w < N + k0) →
                2 ≤ (T ∩ orIn N D w).card → ∃ h ∈ B T, h + N ≤ w := by
              intro T hTS w hw_reach hcardT
              have hwn : N ≤ w := by
                by_contra! hlt
                have h1 := hOrIn_lt w hlt
                have h2 : (T ∩ orIn N D w).card ≤ (orIn N D w).card := Finset.card_le_card Finset.inter_subset_right
                omega
              obtain ⟨h, rfl⟩ : ∃ h, w = N + h := ⟨w - N, by omega⟩
              have hne : (T ∩ orIn N D (N + h)).Nonempty := Finset.card_pos.mp (by omega)
              obtain ⟨u0, hu0⟩ := hne
              have hu0_orIn : u0 ∈ orIn N D (N + h) := (Finset.mem_inter.mp hu0).2
              obtain ⟨hhlen, hhop, _⟩ := (hOrIn_gate h u0).mp hu0_orIn
              have hnb : ¬ BelowF G D h := hOrIn_not_belowF h u0 hu0_orIn
              have horN : h ∈ orN G D := by
                simp only [orN, gatesWhere, Finset.mem_filter, Finset.mem_range]
                exact ⟨hhlen, hhop, hnb⟩
              have hnlam : h ∉ lam G D := by
                intro hlam
                have h1 := hLam h hlam
                have h2 : T ∩ orIn N D (N + h) ⊆ S ∩ orIn N D (N + h) := Finset.inter_subset_inter_right hTS
                have h3 := Finset.card_le_card h2
                omega
              have hw_reach' : ∃ w0 ∈ W, OrReaches N D w0 h := by
                rcases hw_reach with ⟨w0, hw0W, hw0eq | ⟨k0, hreach0, hk0op, hmem, hlt⟩⟩
                · subst hw0eq; exact ⟨N + h, hw0W, hOrReaches_self h hhlen⟩
                · exact ⟨w0, hw0W, hOrReaches_step w0 k0 h hreach0 hk0op (N + h) hmem hlt (hOrReaches_self h hhlen)⟩
              refine ⟨h, ?_, by omega⟩
              simp only [B, Finset.mem_filter, Finset.mem_sdiff]
              exact ⟨⟨horN, hnlam⟩, hw_reach', hcardT⟩
            suffices hmain : ∀ k (T : Finset (Fin N)), T.card = k → T ⊆ S →
                T ⊆ W.biUnion (fun w => orIn N D w) → T.card ≤ W.card + (B T).card by
              exact hmain S.card S rfl Finset.Subset.rfl hSub
            intro k
            induction k using Nat.strong_induction_on with
            | ind k ih =>
              intro T hk hTS hTsub
              by_cases hBe : (B T).Nonempty
              · obtain ⟨h0, hh0, hmin⟩ := Finset.exists_min_image (B T) id hBe
                have hh0_mem := hh0
                simp only [B, Finset.mem_filter, Finset.mem_sdiff] at hh0_mem
                rcases hh0_mem with ⟨⟨horN, _⟩, ⟨w0, hw0W, hreach0⟩, hcard2⟩
                simp only [orN, gatesWhere, Finset.mem_filter, Finset.mem_range] at horN
                rcases horN with ⟨hh0len, hh0op, _⟩
                have hlen2 : (gateAt D h0).inputs.length = 2 := by
                  apply hDAO.2.2; unfold gateAt; simp [List.getD_eq_getElem?_getD, hh0len]
                have hle1 : ∀ b : Fin 2, (T ∩ orIn N D (opnd D h0 b)).card ≤ 1 := by
                  intro b
                  by_contra! hgt1
                  have hmem_in : opnd D h0 b ∈ (gateAt D h0).inputs := by
                    unfold opnd; simp [List.getD_eq_getElem?_getD]
                    have hb : (b : ℕ) < (gateAt D h0).inputs.length := by omega
                    simp [hb, List.getElem_mem]
                  have hlt : opnd D h0 b < N + h0 := hDAO.2.1 h0 hh0len (opnd D h0 b) hmem_in
                  have : ∃ h1 ∈ B T, h1 + N ≤ opnd D h0 b := by
                    apply h_in_B T hTS (opnd D h0 b) ⟨w0, hw0W, Or.inr ⟨h0, hreach0, hh0op, hmem_in, hlt⟩⟩
                    omega
                  rcases this with ⟨h1, hh1, h1le⟩
                  have hle := hmin h1 hh1
                  simp only [id_eq] at hle
                  omega
                have hsub_union : T ∩ orIn N D (N + h0) ⊆
                    (T ∩ orIn N D (opnd D h0 0)) ∪ (T ∩ orIn N D (opnd D h0 1)) := by
                  intro u hu
                  rw [Finset.mem_inter, hOrIn_gate] at hu
                  rcases hu with ⟨huT, _, _, w, hw, _, huw⟩
                  have hidx : ∃ b : Fin 2, w = opnd D h0 b := by
                    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hw
                    have hi2 : i < 2 := by omega
                    refine ⟨⟨i, hi2⟩, ?_⟩
                    unfold opnd; simp [List.getD_eq_getElem?_getD, hi]
                  rcases hidx with ⟨b, rfl⟩
                  fin_cases b
                  · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨huT, huw⟩)
                  · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨huT, huw⟩)
                have hsum : (T ∩ orIn N D (opnd D h0 0)).card + (T ∩ orIn N D (opnd D h0 1)).card ≥ 2 := by
                  have := Finset.card_le_card hsub_union
                  have := Finset.card_union_le (T ∩ orIn N D (opnd D h0 0)) (T ∩ orIn N D (opnd D h0 1))
                  omega
                have hc0 : (T ∩ orIn N D (opnd D h0 0)).card = 1 := by
                  have := hle1 0; have := hle1 1; omega
                have hc1 : (T ∩ orIn N D (opnd D h0 1)).card = 1 := by
                  have := hle1 0; have := hle1 1; omega
                obtain ⟨v0, hv0⟩ := Finset.card_eq_one.mp hc0
                obtain ⟨v1, hv1⟩ := Finset.card_eq_one.mp hc1
                have hv0_mem : v0 ∈ T ∩ orIn N D (opnd D h0 0) := by rw [hv0]; exact Finset.mem_singleton_self v0
                have hv1_mem : v1 ∈ T ∩ orIn N D (opnd D h0 1) := by rw [hv1]; exact Finset.mem_singleton_self v1
                have hv01 : v0 ≠ v1 := by
                  intro heq; subst heq
                  have : (T ∩ orIn N D (N + h0)).card ≤ 1 := by
                    have h1 := Finset.card_le_card hsub_union
                    rw [hv0, hv1, Finset.union_idempotent, Finset.card_singleton] at h1
                    exact h1
                  omega
                let T' := T.erase v0
                have hv0T : v0 ∈ T := (Finset.mem_inter.mp hv0_mem).1
                have hk' : T'.card < k := by rw [← hk]; exact Finset.card_erase_lt_of_mem hv0T
                have hBT' : (B T').card + 1 ≤ (B T).card := by
                  have hsubB : B T' ⊆ (B T).erase h0 := by
                    intro h hh
                    rw [Finset.mem_erase]
                    refine ⟨?_, hB_sub T' T (Finset.erase_subset _ _) hh⟩
                    intro heq; subst heq
                    simp only [B, Finset.mem_filter] at hh
                    have hsub0 : T' ∩ orIn N D (N + h) ⊆ {v1} := by
                      intro u hu
                      have hu' := hsub_union (Finset.mem_inter.mpr ⟨Finset.erase_subset _ _ (Finset.mem_inter.mp hu).1, (Finset.mem_inter.mp hu).2⟩)
                      rcases Finset.mem_union.mp hu' with hu0 | hu1
                      · rw [hv0, Finset.mem_singleton] at hu0; subst hu0
                        exact absurd (Finset.mem_inter.mp hu).1 (Finset.notMem_erase _ _)
                      · rw [hv1] at hu1; exact hu1
                    have := Finset.card_le_card hsub0; simp at this; omega
                  have := Finset.card_le_card hsubB
                  rw [Finset.card_erase_of_mem hh0] at this
                  have : 0 < (B T).card := Finset.card_pos.mpr ⟨h0, hh0⟩
                  omega
                have hih := ih T'.card hk' T' rfl (Finset.Subset.trans (Finset.erase_subset _ _) hTS)
                  (Finset.Subset.trans (Finset.erase_subset _ _) hTsub)
                have hcardT : T.card = T'.card + 1 := (Finset.card_erase_add_one hv0T).symm
                omega
              · rw [Finset.not_nonempty_iff_eq_empty] at hBe
                have hcardW : ∀ w ∈ W, (T ∩ orIn N D w).card ≤ 1 := by
                  intro w hw
                  by_contra! hgt1
                  obtain ⟨h, hh, _⟩ := h_in_B T hTS w ⟨w, hw, Or.inl rfl⟩ hgt1
                  rw [hBe] at hh; exact absurd hh (Finset.notMem_empty _)
                have hcov : T ⊆ W.biUnion (fun w => T ∩ orIn N D w) := by
                  intro v hv
                  obtain ⟨w, hwW, hvw⟩ := Finset.mem_biUnion.mp (hTsub hv)
                  exact Finset.mem_biUnion.mpr ⟨w, hwW, Finset.mem_inter.mpr ⟨hv, hvw⟩⟩
                calc T.card
                  _ ≤ (W.biUnion (fun w => T ∩ orIn N D w)).card := Finset.card_le_card hcov
                  _ ≤ ∑ w ∈ W, (T ∩ orIn N D w).card := Finset.card_biUnion_le
                  _ ≤ ∑ _w ∈ W, 1 := Finset.sum_le_sum (fun w hw => hcardW w hw)
                  _ = W.card := by simp
                  _ ≤ W.card + (B T).card := Nat.le_add_right _ _
          have hLam_bound : ∀ h ∈ lam G D, ∀ u : Fin N,
              ((orIn N D (N + h)).filter fun v => s(u, v) ∈ Ustar G D).card ≤ 1 := by
            intro h hh u
            simp only [lam, Finset.mem_filter] at hh
            rcases hh with ⟨_, _, _, a, ha, b, hcard1, hreach⟩
            obtain ⟨z, hz⟩ := Finset.card_eq_one.mp hcard1
            have hz_mem : z ∈ PEqualNP.TopForm.side D a (1 - b) := by
              rw [hz]; exact Finset.mem_singleton_self z
            have hAdjStar : ∀ v ∈ orIn N D (N + h), G.Adj z v ∧ s(z, v) ∈ starEdges G D := by
              intro v hv
              have hv_side : v ∈ PEqualNP.TopForm.side D a b := hOrIn_mono (opnd D a b) h v hreach hv
              fin_cases b
              · have h1 := hTop_adj a ha v hv_side z (by simpa using hz_mem)
                rw [SimpleGraph.adj_comm, Sym2.eq_swap] at h1; exact h1
              · exact hTop_adj a ha z (by simpa using hz_mem) v hv_side
            by_cases huz : u = z
            · subst huz
              have hempty : ((orIn N D (N + h)).filter fun v => s(u, v) ∈ Ustar G D) = ∅ := by
                rw [Finset.filter_eq_empty_iff]
                intro v hv hU'
                exact (Finset.mem_sdiff.mp hU').2 (hAdjStar v hv).2
              rw [hempty, Finset.card_empty]; omega
            · have hsub : ((orIn N D (N + h)).filter fun v => s(u, v) ∈ Ustar G D) ⊆
                  (Finset.univ.filter fun w => G.Adj u w ∧ G.Adj z w) := by
                intro v hv
                simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
                have hUv : s(u, v) ∈ G.edgeFinset := (Finset.mem_sdiff.mp hv.2).1
                rw [SimpleGraph.mem_edgeFinset] at hUv
                exact ⟨hUv, (hAdjStar v hv.1).1⟩
              exact le_trans (Finset.card_le_card hsub) (hNo4 u z huz)
          have hWire_orReaches_val : ∀ w k x, OrReaches N D w k → wireVal (N + k) x = true →
              wireVal w x = true := by
            intro w k x hreach hkval
            obtain ⟨r, hklen⟩ := orReaches_reach k w hreach
            induction r using Relation.ReflTransGen.head_induction_on with
            | refl => exact hkval
            | @head a c hstep hrest ih =>
              obtain ⟨k', hk', rfl, hkop, hcin, _⟩ := hstep
              rw [wireVal_gate_or k' hk' hkop x]
              have hlen2 : (gateAt D k').inputs.length = 2 := by
                apply hDAO.2.2; unfold gateAt; simp [List.getD_eq_getElem?_getD, hk']
              obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hcin
              have hi2 : i < 2 := by omega
              have ihc := ih (reach_orReaches hrest k rfl hklen)
              have hceq : (gateAt D k').inputs[i] = opnd D k' ⟨i, hi2⟩ := by
                unfold opnd; simp [List.getD_eq_getElem?_getD, hi]
              rw [hceq] at ihc
              have hi01 : i = 0 ∨ i = 1 := by omega
              rcases hi01 with rfl | rfl
              · exact Or.inl ihc
              · exact Or.inr ihc
          have hU_g : ∀ e ∈ Ustar G D, ∃ a ∈ tops G D, ∃ u v : Fin N, e = s(u, v) ∧ u ≠ v ∧
              ∃ b_a : Fin 2, OrReaches N D (opnd D a b_a) g ∧ wireVal (N + g) (pairInput u v) = true ∧
                (¬ ∃ g' < D.gates.length, (gateAt D g').op = GateOp.and ∧
                  OrReaches N D (opnd D a (1 - b_a)) g') ∧
                (u ∈ PEqualNP.TopForm.side D a (1 - b_a) ∨ v ∈ PEqualNP.TopForm.side D a (1 - b_a)) := by
            intro e heU
            obtain ⟨a, ha, u, v, rfl, huv, hside⟩ := hU_witness e heU
            have hAnd_eq_g : ∀ b g', g' < D.gates.length → (gateAt D g').op = GateOp.and →
                OrReaches N D (opnd D a b) g' → g' = g := by
              intro b g' hg'len hg'op hreach
              rcases hAnd_split g' hg'len hg'op with htop | hjunk
              · exact False.elim (hTop_not_in_cone a ha b g' hreach htop)
              · rw [hg_eq, Finset.mem_singleton] at hjunk; exact hjunk
            have hex_b : ∃ b_a : Fin 2, OrReaches N D (opnd D a b_a) g ∧
                wireVal (N + g) (pairInput u v) = true := by
              by_cases h0 : ∃ g' < D.gates.length, (gateAt D g').op = GateOp.and ∧
                  OrReaches N D (opnd D a 0) g' ∧ wireVal (N + g') (pairInput u v) = true
              · obtain ⟨g', hg'len, hg'op, hreach, hg'val⟩ := h0
                obtain rfl := hAnd_eq_g 0 g' hg'len hg'op hreach
                exact ⟨0, hreach, hg'val⟩
              · have hs0 := (hside 0).resolve_right h0
                by_cases h1 : ∃ g' < D.gates.length, (gateAt D g').op = GateOp.and ∧
                    OrReaches N D (opnd D a 1) g' ∧ wireVal (N + g') (pairInput u v) = true
                · obtain ⟨g', hg'len, hg'op, hreach, hg'val⟩ := h1
                  obtain rfl := hAnd_eq_g 1 g' hg'len hg'op hreach
                  exact ⟨1, hreach, hg'val⟩
                · have hs1 := (hside 1).resolve_right h1
                  exfalso
                  have hstar : s(u, v) ∈ starEdges G D := by
                    simp only [starEdges, Finset.mem_biUnion, Finset.mem_image, Finset.mem_product]
                    rcases hs0 with hu0 | hv0 <;> rcases hs1 with hu1 | hv1
                    · exact absurd ⟨hu0, hu1⟩ (hTop_no_self a ha u)
                    · exact ⟨a, ha, (u, v), ⟨hu0, hv1⟩, rfl⟩
                    · exact ⟨a, ha, (v, u), ⟨hv0, hu1⟩, Sym2.eq_swap⟩
                    · exact absurd ⟨hv0, hv1⟩ (hTop_no_self a ha v)
                  exact (Finset.mem_sdiff.mp heU).2 hstar
            obtain ⟨b_a, hreach_ba, hgval⟩ := hex_b
            have hno_other : ¬ ∃ g' < D.gates.length, (gateAt D g').op = GateOp.and ∧
                OrReaches N D (opnd D a (1 - b_a)) g' := by
              intro ⟨g', hg'len, hg'op, hreach'⟩
              have hg'eq := hAnd_eq_g (1 - b_a) g' hg'len hg'op hreach'
              rw [hg'eq] at hreach'
              apply hg_nbel
              intro x hx
              have ha' := ha
              simp only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range] at ha'
              apply ha'.2.2 x
              rw [gateVal_eq_wireVal, wireVal_gate_and a ha'.1 ha'.2.1 x]
              rw [gateVal_eq_wireVal] at hx
              have hba := hWire_orReaches_val (opnd D a b_a) g x hreach_ba hx
              have h1ba := hWire_orReaches_val (opnd D a (1 - b_a)) g x hreach' hx
              fin_cases b_a
              · exact ⟨hba, h1ba⟩
              · exact ⟨h1ba, hba⟩
            have hside_other : u ∈ PEqualNP.TopForm.side D a (1 - b_a) ∨
                v ∈ PEqualNP.TopForm.side D a (1 - b_a) := by
              have h_ := hside (1 - b_a)
              rcases h_ with hs | ⟨g', hg'len, hg'op, hreach', _⟩
              · exact hs
              · exact False.elim (hno_other ⟨g', hg'len, hg'op, hreach'⟩)
            exact ⟨a, ha, u, v, rfl, huv, b_a, hreach_ba, hgval, hno_other, hside_other⟩
          have hSide_wmax : ∀ a ∈ tops G D, ∀ b_a : Fin 2, OrReaches N D (opnd D a b_a) g →
              ∀ w ∈ PEqualNP.TopForm.side D a (1 - b_a), w ∈ wmax G D g := by
            intro a ha b_a hreach w hw
            simp only [wmax, Finset.mem_filter, Finset.mem_univ, true_and]
            intro x hxg hxw
            have ha' := ha
            simp only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range] at ha'
            apply ha'.2.2 x
            rw [gateVal_eq_wireVal, wireVal_gate_and a ha'.1 ha'.2.1 x]
            rw [gateVal_eq_wireVal] at hxg
            have hba := hWire_orReaches_val (opnd D a b_a) g x hreach hxg
            have h1ba := wireVal_orIn (opnd D a (1 - b_a)) w x hw hxw
            fin_cases b_a
            · exact ⟨hba, h1ba⟩
            · exact ⟨h1ba, hba⟩
          have hMix_reach : ∀ w, (orIn N D w).Nonempty → OrReaches N D w g →
              ∃ h ∈ orN G D \ lam G D, g < h ∧ OrReaches N D w h ∧ (orIn N D (N + h)).Nonempty := by
            intro w
            induction w using Nat.strong_induction_on with
            | ind w ih =>
              intro hwne hreach
              have hnw : N ≤ w := hreach.1
              obtain ⟨k, rfl⟩ : ∃ k, w = N + k := ⟨w - N, by omega⟩
              obtain ⟨u0, hu0⟩ := hwne
              obtain ⟨hklen, hkop, w_in, hw_mem, hw_lt, hu0_w⟩ := (hOrIn_gate k u0).mp hu0
              have hne_kg : k ≠ g := by
                intro heq; subst heq; rw [hg_op] at hkop; cases hkop
              obtain ⟨hklen', hrec⟩ := (orReaches_iff k g).mp hreach
              rcases hrec with rfl | ⟨_, i, hi_mem, hi_lt, hi_reach⟩
              · exact absurd rfl hne_kg
              · have hlen2 : (gateAt D k).inputs.length = 2 := by
                  apply hDAO.2.2; unfold gateAt; simp [List.getD_eq_getElem?_getD, hklen]
                obtain ⟨idx, hidx, rfl⟩ := List.mem_iff_getElem.mp hi_mem
                have hidx2 : idx < 2 := by omega
                let c : Fin 2 := ⟨idx, hidx2⟩
                have hceq : (gateAt D k).inputs[idx] = opnd D k c := by
                  unfold opnd; simp [c, List.getD_eq_getElem?_getD, hidx]
                rw [hceq] at hi_reach hi_lt
                by_cases hc_ne : (orIn N D (opnd D k c)).Nonempty
                · obtain ⟨h, hh, hgh, hreach_h, hne_h⟩ := ih (opnd D k c) hi_lt hc_ne hi_reach
                  have hmem_c : opnd D k c ∈ (gateAt D k).inputs := by
                    unfold opnd; simp [List.getD_eq_getElem?_getD]
                    have hc' : (c : ℕ) < (gateAt D k).inputs.length := by omega
                    simp [hc', List.getElem_mem]
                  exact ⟨h, hh, hgh, hOrReaches_step (N + k) k h (hOrReaches_self k hklen) hkop
                    (opnd D k c) hmem_c hi_lt hreach_h, hne_h⟩
                · have hk_orN : k ∈ orN G D := by
                    simp only [orN, gatesWhere, Finset.mem_filter, Finset.mem_range]
                    exact ⟨hklen, hkop, hOrIn_not_belowF k u0 hu0⟩
                  have hk_nlam : k ∉ lam G D := by
                    intro hlam
                    simp only [lam, Finset.mem_filter] at hlam
                    have hidx01 : idx = 0 ∨ idx = 1 := by omega
                    rcases hidx01 with rfl | rfl
                    · exact absurd hlam.2.1 hc_ne
                    · exact absurd hlam.2.2.1 hc_ne
                  have hgk : g < k := by
                    have h1 := orReaches_le (opnd D k c) g hi_reach
                    omega
                  exact ⟨k, Finset.mem_sdiff.mpr ⟨hk_orN, hk_nlam⟩, hgk, hOrReaches_self k hklen,
                    ⟨u0, hu0⟩⟩
          let H := G.deleteEdges ↑(Ustar G D)
          let coverSize (s : ℕ) := ∃ T : Finset (Fin N), H.IsVertexCover (↑T) ∧ T.card = s
          have univCover : H.IsVertexCover (↑(Finset.univ : Finset (Fin N))) := by
            intro a b _; exact Or.inl (by simp)
          have existsCover : ∃ s, coverSize s := ⟨_, Finset.univ, univCover, rfl⟩
          obtain ⟨K, hKcovers, hKcard⟩ := Nat.find_spec existsCover
          have hK : IsMinCover H K := ⟨hKcovers, fun T hT =>
            hKcard ▸ Nat.find_min' existsCover (show coverSize T.card from ⟨T, hT, rfl⟩)⟩
          have hchargeK := (charge (n + m) G D hNo4 hEdges hDleast hDtop).2 K hK
          let W0 : Finset (Fin N) := (wmax G D g).filter fun u => u ∈ S0
          let W1 : Finset (Fin N) := (wmax G D g).filter fun v => v ∈ S1
          have hW0_nS1 : ∀ u ∈ W0, u ∉ S1 := by
            intro u hu huS1
            simp only [W0, Finset.mem_filter, wmax, Finset.mem_univ, true_and] at hu
            have hval : gateVal N D g (fun i => decide (i = u)) = true := by
              rw [gateVal_eq_wireVal, hg_iff]
              exact ⟨⟨u, hu.2, by simp⟩, ⟨u, huS1, by simp⟩⟩
            have hf := hu.1 (fun i => decide (i = u)) hval (by simp)
            rw [hSingle_false u] at hf; cases hf
          have hW1_nS0 : ∀ v ∈ W1, v ∉ S0 := by
            intro v hv hvS0
            simp only [W1, Finset.mem_filter, wmax, Finset.mem_univ, true_and] at hv
            have hval : gateVal N D g (fun i => decide (i = v)) = true := by
              rw [gateVal_eq_wireVal, hg_iff]
              exact ⟨⟨v, hvS0, by simp⟩, ⟨v, hv.2, by simp⟩⟩
            have hf := hv.1 (fun i => decide (i = v)) hval (by simp)
            rw [hSingle_false v] at hf; cases hf
          have hwmax_adj : ∀ w ∈ wmax G D g, ∀ u ∈ S0, ∀ v ∈ S1,
              w = u ∨ w = v → u ≠ v → G.Adj u v := by
            intro w hw u hu v hv hwuv huv
            simp only [wmax, Finset.mem_filter, Finset.mem_univ, true_and] at hw
            have hval : gateVal N D g (pairInput u v) = true := by
              rw [gateVal_eq_wireVal, hg_iff]
              exact ⟨⟨u, hu, by simp [pairInput]⟩, ⟨v, hv, by simp [pairInput]⟩⟩
            have hxw : pairInput u v w = true := by
              rcases hwuv with rfl | rfl <;> simp [pairInput]
            have hf := hw (pairInput u v) hval hxw
            unfold graphFun at hf
            simp only [Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or,
              decide_eq_true_eq] at hf
            rcases hf with ⟨p, q, hadj, hp, hq⟩
            have hp' : p = u ∨ p = v := by simpa [pairInput] using hp
            have hq' : q = u ∨ q = v := by simpa [pairInput] using hq
            rcases hp' with rfl | rfl <;> rcases hq' with rfl | rfl
            · exact absurd hadj (G.loopless.irrefl _)
            · exact hadj
            · exact hadj.symm
            · exact absurd hadj (G.loopless.irrefl _)
          have hW0_adj_S1 : ∀ u ∈ W0, ∀ v ∈ S1, G.Adj u v := by
            intro u hu v hv
            have huw : u ∈ wmax G D g := (Finset.mem_filter.mp hu).1
            have huS0 : u ∈ S0 := (Finset.mem_filter.mp hu).2
            have huv : u ≠ v := fun heq => hW0_nS1 u hu (heq ▸ hv)
            exact hwmax_adj u huw u huS0 v hv (Or.inl rfl) huv
          have hW1_adj_S0 : ∀ v ∈ W1, ∀ u ∈ S0, G.Adj u v := by
            intro v hv u hu
            have hvw : v ∈ wmax G D g := (Finset.mem_filter.mp hv).1
            have hvS1 : v ∈ S1 := (Finset.mem_filter.mp hv).2
            have huv : u ≠ v := fun heq => hW1_nS0 v hv (heq ▸ hu)
            exact hwmax_adj v hvw u hu v hvS1 (Or.inr rfl) huv
          have hW0_card : 2 ≤ S1.card → W0.card ≤ 1 := by
            intro hS1
            rw [Finset.card_le_one]
            intro u1 hu1 u2 hu2
            by_contra hne
            have hsub : S1 ⊆ Finset.univ.filter (fun v => G.Adj u1 v ∧ G.Adj u2 v) := by
              intro v hv
              simp only [Finset.mem_filter, Finset.mem_univ, true_and]
              exact ⟨hW0_adj_S1 u1 hu1 v hv, hW0_adj_S1 u2 hu2 v hv⟩
            have h1 := le_trans hS1 (Finset.card_le_card hsub)
            have h2 := hNo4 u1 u2 hne
            exact absurd (le_trans h1 h2) (by decide)
          have hW1_card : 2 ≤ S0.card → W1.card ≤ 1 := by
            intro hS0
            rw [Finset.card_le_one]
            intro v1 hv1 v2 hv2
            by_contra hne
            have hsub : S0 ⊆ Finset.univ.filter (fun u => G.Adj v1 u ∧ G.Adj v2 u) := by
              intro u hu
              simp only [Finset.mem_filter, Finset.mem_univ, true_and]
              exact ⟨(hW1_adj_S0 v1 hv1 u hu).symm, (hW1_adj_S0 v2 hv2 u hu).symm⟩
            have h1 := le_trans hS0 (Finset.card_le_card hsub)
            have h2 := hNo4 v1 v2 hne
            exact absurd (le_trans h1 h2) (by decide)
          have hB_lt_g : ∀ (W : Finset ℕ), (∀ w ∈ W, w = opnd D g 0 ∨ w = opnd D g 1) →
              ∀ S, ∀ h ∈ (orN G D \ lam G D).filter (fun h =>
                (∃ w ∈ W, OrReaches N D w h) ∧ 2 ≤ (S ∩ orIn N D (N + h)).card), h < g := by
            intro W hW S h hh
            simp only [Finset.mem_filter] at hh
            obtain ⟨w, hwW, hreach⟩ := hh.2.1
            have hle := orReaches_le w h hreach
            rcases hW w hwW with rfl | rfl
            · have hmem_in : opnd D g 0 ∈ (gateAt D g).inputs := by
                have hlen2 : (gateAt D g).inputs.length = 2 := by
                  apply hDAO.2.2; unfold gateAt; simp [List.getD_eq_getElem?_getD, hg_len]
                unfold opnd; simp [List.getD_eq_getElem?_getD]
                have hb : (0 : ℕ) < (gateAt D g).inputs.length := by omega
                simp [hb, List.getElem_mem]
              have hlt := hDAO.2.1 g hg_len (opnd D g 0) hmem_in
              omega
            · have hmem_in : opnd D g 1 ∈ (gateAt D g).inputs := by
                have hlen2 : (gateAt D g).inputs.length = 2 := by
                  apply hDAO.2.2; unfold gateAt; simp [List.getD_eq_getElem?_getD, hg_len]
                unfold opnd; simp [List.getD_eq_getElem?_getD]
                have hb : (1 : ℕ) < (gateAt D g).inputs.length := by omega
                simp [hb, List.getElem_mem]
              have hlt := hDAO.2.1 g hg_len (opnd D g 1) hmem_in
              omega
          -- Helper for 1-vertex cover bound using S_side = N_U(x)
          have hOneCover : ∀ (x : Fin N) (b_op : Fin 2),
              (∀ e ∈ Ustar G D, x ∈ e ∧ ∃ y ∈ orIn N D (opnd D g b_op), y ≠ x ∧ e = s(x, y)) →
              ∃ K X, IsMinCover H K ∧ (∀ e ∈ Ustar G D, ∃ v ∈ K ∪ X, v ∈ e) ∧
                (K ∪ X).card + (Ustar G D).card ≤ (tops G D \ centreless G D).card +
                  2 * (centreless G D).card + (junk G D).card + (orN G D \ lam G D).card := by
            intro x b_op hx_cov
            let Nx : Finset (Fin N) := (orIn N D (opnd D g b_op)).filter fun y => s(x, y) ∈ Ustar G D
            have hU_sub_Nx : Ustar G D ⊆ Nx.image (fun y => s(x, y)) := by
              intro e heU
              obtain ⟨_, y, hy_in, _, rfl⟩ := hx_cov e heU
              exact Finset.mem_image.mpr ⟨y, Finset.mem_filter.mpr ⟨hy_in, heU⟩, rfl⟩
            have hNx_sub : Nx ⊆ ({opnd D g b_op} : Finset ℕ).biUnion (fun w => orIn N D w) := by
              intro y hy; simp only [Finset.mem_biUnion, Finset.mem_singleton, exists_eq_left]
              exact (Finset.mem_filter.mp hy).1
            have hNx_lam : ∀ h ∈ lam G D, (Nx ∩ orIn N D (N + h)).card ≤ 1 := by
              intro h hh
              have hsub : Nx ∩ orIn N D (N + h) ⊆
                  (orIn N D (N + h)).filter fun y => s(x, y) ∈ Ustar G D := by
                intro y hy
                rw [Finset.mem_inter] at hy
                exact Finset.mem_filter.mpr ⟨hy.2, (Finset.mem_filter.mp hy.1).2⟩
              exact le_trans (Finset.card_le_card hsub) (hLam_bound h hh x)
            have hGML_x := hGML {opnd D g b_op} Nx hNx_sub hNx_lam
            simp only [Finset.card_singleton] at hGML_x
            let Bx := (orN G D \ lam G D).filter fun h =>
              (∃ w ∈ ({opnd D g b_op} : Finset ℕ), OrReaches N D w h) ∧ 2 ≤ (Nx ∩ orIn N D (N + h)).card
            have hGML_x' : Nx.card ≤ 1 + Bx.card := hGML_x
            have hU_le : (Ustar G D).card ≤ 1 + Bx.card :=
              le_trans (Finset.card_le_card hU_sub_Nx) (le_trans (Finset.card_image_le) hGML_x')
            obtain ⟨e0, he0⟩ := hU
            obtain ⟨a0, ha0, _, _, _, _, b0, hreach0, _, _, _⟩ := hU_g e0 he0
            have hExtra : 1 ≤ 2 * (centreless G D).card + ((orN G D \ lam G D) \ Bx).card := by
              by_cases ha0c : a0 ∈ centreless G D
              · have : 0 < (centreless G D).card := Finset.card_pos.mpr ⟨a0, ha0c⟩
                omega
              · have ha0_sdiff : a0 ∈ tops G D \ centreless G D := Finset.mem_sdiff.mpr ⟨ha0, ha0c⟩
                simp only [centreless, Finset.mem_filter, not_and, not_or] at ha0c
                have hne_side : (PEqualNP.TopForm.side D a0 b0).Nonempty :=
                  Finset.nonempty_iff_ne_empty.mpr (by
                    fin_cases b0
                    · exact (ha0c ha0).1
                    · exact (ha0c ha0).2)
                obtain ⟨h_mix, hh_mem, hgh, _, _⟩ := hMix_reach (opnd D a0 b0) hne_side hreach0
                have hh_not_Bx : h_mix ∉ Bx := by
                  intro hbx
                  have hlt_g := hB_lt_g {opnd D g b_op} (fun w hw => by
                    rw [Finset.mem_singleton] at hw; subst hw
                    fin_cases b_op <;> simp) Nx h_mix hbx
                  omega
                have : 0 < ((orN G D \ lam G D) \ Bx).card :=
                  Finset.card_pos.mpr ⟨h_mix, Finset.mem_sdiff.mpr ⟨hh_mem, hh_not_Bx⟩⟩
                omega
            have hBx_sub : Bx ⊆ orN G D \ lam G D := Finset.filter_subset _ _
            have hBx_split := Finset.card_sdiff_add_card_eq_card hBx_sub
            refine ⟨K, {x}, hK, fun e he => ?_, ?_⟩
            · exact ⟨x, Finset.mem_union_right _ (Finset.mem_singleton_self x), (hx_cov e he).1⟩
            · have hKU : (K ∪ {x}).card ≤ K.card + 1 :=
                le_trans (Finset.card_union_le K {x}) (by simp)
              omega
          -- Case split on (S0 ∩ S1).Nonempty
          by_cases hInter : (S0 ∩ S1).Nonempty
          · have hwmax_nI : ∀ z ∈ wmax G D g, z ∉ S0 ∩ S1 := by
              intro z hz hzm
              rw [Finset.mem_inter] at hzm
              simp only [wmax, Finset.mem_filter, Finset.mem_univ, true_and] at hz
              have hval : gateVal N D g (fun i => decide (i = z)) = true := by
                rw [gateVal_eq_wireVal, hg_iff]
                exact ⟨⟨z, hzm.1, by simp⟩, ⟨z, hzm.2, by simp⟩⟩
              have hf := hz (fun i => decide (i = z)) hval (by simp)
              rw [hSingle_false z] at hf; cases hf
            have hwmax_adj_I : ∀ z ∈ wmax G D g, ∀ w ∈ S0 ∩ S1, G.Adj z w := by
              intro z hz w hw
              have hzw : z ≠ w := fun h => hwmax_nI z hz (h ▸ hw)
              rw [Finset.mem_inter] at hw
              simp only [wmax, Finset.mem_filter, Finset.mem_univ, true_and] at hz
              have hval : gateVal N D g (pairInput z w) = true := by
                rw [gateVal_eq_wireVal, hg_iff]
                exact ⟨⟨w, hw.1, by simp [pairInput]⟩, ⟨w, hw.2, by simp [pairInput]⟩⟩
              have hf := hz (pairInput z w) hval (by simp [pairInput])
              unfold graphFun at hf
              simp only [Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or,
                decide_eq_true_eq] at hf
              rcases hf with ⟨p, q, hadj, hp, hq⟩
              have hp' : p = z ∨ p = w := by simpa [pairInput] using hp
              have hq' : q = z ∨ q = w := by simpa [pairInput] using hq
              rcases hp' with rfl | rfl <;> rcases hq' with rfl | rfl
              · exact absurd hadj (G.loopless.irrefl _)
              · exact hadj
              · exact hadj.symm
              · exact absurd hadj (G.loopless.irrefl _)
            by_cases hI2 : 2 ≤ (S0 ∩ S1).card
            · -- Subcase 2a: 2 ≤ (S0 ∩ S1).card => wmax.card ≤ 1
              have hwmax_le1 : (wmax G D g).card ≤ 1 := by
                rw [Finset.card_le_one]
                intro z1 hz1 z2 hz2
                by_contra hne
                obtain ⟨w1, hw1, w2, hw2, hw12⟩ := Finset.one_lt_card.mp (by omega : 1 < (S0 ∩ S1).card)
                have hsub : ({w1, w2} : Finset (Fin N)) ⊆
                    (Finset.univ : Finset (Fin N)).filter fun w => G.Adj z1 w ∧ G.Adj z2 w := by
                  intro c hc
                  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
                  rcases Finset.mem_insert.mp hc with hcw1 | hc2
                  · rw [hcw1]; exact ⟨hwmax_adj_I z1 hz1 w1 hw1, hwmax_adj_I z2 hz2 w1 hw1⟩
                  · rw [Finset.mem_singleton] at hc2; rw [hc2]
                    exact ⟨hwmax_adj_I z1 hz1 w2 hw2, hwmax_adj_I z2 hz2 w2 hw2⟩
                have h4c := hNo4 z1 z2 hne
                have hcard := Finset.card_le_card hsub
                rw [Finset.card_pair hw12] at hcard
                exact absurd (le_trans hcard h4c) (by omega)
              obtain ⟨e0, he0⟩ := hU
              obtain ⟨a0, ha0, p0, q0, _, _, b0, hreach0, _, _, hside0⟩ := hU_g e0 he0
              have hz0_ex : ∃ z0 ∈ wmax G D g, True := by
                rcases hside0 with hp0 | hq0
                · exact ⟨p0, hSide_wmax a0 ha0 b0 hreach0 p0 hp0, trivial⟩
                · exact ⟨q0, hSide_wmax a0 ha0 b0 hreach0 q0 hq0, trivial⟩
              obtain ⟨z0, hz0, _⟩ := hz0_ex
              by_cases hz0_S0 : z0 ∈ S0
              · have hz0_nS1 : z0 ∉ S1 := fun h => hwmax_nI z0 hz0 (Finset.mem_inter.mpr ⟨hz0_S0, h⟩)
                apply hOneCover z0 1
                intro e he
                obtain ⟨a, ha, p, q, rfl, hpq, b_a, hreach, hgval, _, hside⟩ := hU_g e he
                have hz_eq : p = z0 ∨ q = z0 := by
                  rcases hside with hp | hq
                  · exact Or.inl (Finset.card_le_one.mp hwmax_le1 p (hSide_wmax a ha b_a hreach p hp) z0 hz0)
                  · exact Or.inr (Finset.card_le_one.mp hwmax_le1 q (hSide_wmax a ha b_a hreach q hq) z0 hz0)
                rw [hg_iff] at hgval
                obtain ⟨_, ⟨v, hv, hv_eq⟩⟩ := hgval
                have hv' : v = p ∨ v = q := by simpa [pairInput] using hv_eq
                rcases hz_eq with rfl | rfl
                · have hvq : v = q := hv'.resolve_left (fun h => hz0_nS1 (h ▸ hv))
                  subst hvq
                  exact ⟨Sym2.mem_mk_left _ _, v, hv, hpq.symm, rfl⟩
                · have hvp : v = p := hv'.resolve_right (fun h => hz0_nS1 (h ▸ hv))
                  subst hvp
                  exact ⟨Sym2.mem_mk_right _ _, v, hv, hpq, Sym2.eq_swap⟩
              · apply hOneCover z0 0
                intro e he
                obtain ⟨a, ha, p, q, rfl, hpq, b_a, hreach, hgval, _, hside⟩ := hU_g e he
                have hz_eq : p = z0 ∨ q = z0 := by
                  rcases hside with hp | hq
                  · exact Or.inl (Finset.card_le_one.mp hwmax_le1 p (hSide_wmax a ha b_a hreach p hp) z0 hz0)
                  · exact Or.inr (Finset.card_le_one.mp hwmax_le1 q (hSide_wmax a ha b_a hreach q hq) z0 hz0)
                rw [hg_iff] at hgval
                obtain ⟨⟨u, hu, hu_eq⟩, _⟩ := hgval
                have hu' : u = p ∨ u = q := by simpa [pairInput] using hu_eq
                rcases hz_eq with rfl | rfl
                · have huq : u = q := hu'.resolve_left (fun h => hz0_S0 (h ▸ hu))
                  subst huq
                  exact ⟨Sym2.mem_mk_left _ _, u, hu, hpq.symm, rfl⟩
                · have hup : u = p := hu'.resolve_right (fun h => hz0_S0 (h ▸ hu))
                  subst hup
                  exact ⟨Sym2.mem_mk_right _ _, u, hu, hpq, Sym2.eq_swap⟩
            · -- Subcase 2b: (S0 ∩ S1).card = 1
              have hI1 : (S0 ∩ S1).card = 1 := by
                have := Finset.card_pos.mpr hInter; omega
              obtain ⟨w, hw_eq⟩ := Finset.card_eq_one.mp hI1
              have hw_mem : w ∈ S0 ∩ S1 := by rw [hw_eq]; exact Finset.mem_singleton_self w
              have hw_S0 : w ∈ S0 := (Finset.mem_inter.mp hw_mem).1
              have hw_S1 : w ∈ S1 := (Finset.mem_inter.mp hw_mem).2
              have hI_iff : ∀ x, x ∈ S0 ∩ S1 ↔ x = w := by
                intro x; rw [hw_eq, Finset.mem_singleton]
              have hW01_empty : W0 = ∅ ∨ W1 = ∅ := by
                by_contra hboth
                push Not at hboth
                obtain ⟨u0, hu0⟩ := hboth.1
                obtain ⟨v0, hv0⟩ := hboth.2
                have hadj_uv : G.Adj u0 v0 := hW0_adj_S1 u0 hu0 v0 (Finset.mem_filter.mp hv0).2
                have hadj_uw : G.Adj u0 w := hW0_adj_S1 u0 hu0 w hw_S1
                have hadj_vw : G.Adj v0 w := (hW1_adj_S0 v0 hv0 w hw_S0).symm
                obtain ⟨col, hcol⟩ := hBip
                have h1 : col u0 ≠ col v0 := hcol hadj_uv
                have h2 : col u0 ≠ col w := hcol hadj_uw
                have h3 : col v0 ≠ col w := hcol hadj_vw
                omega
              let W_out : Finset (Fin N) :=
                (wmax G D g \ (S0 ∪ S1)).filter fun z => s(w, z) ∈ Ustar G D
              by_cases hWout : W_out = ∅
              · -- When W_out = ∅, every edge in Ustar has an endpoint in W0 ∪ W1
                have hU_W01 : ∀ e ∈ Ustar G D, ∃ u ∈ S0, ∃ v ∈ S1, e = s(u, v) ∧ u ≠ v ∧
                    (u ∈ W0 ∨ v ∈ W1) := by
                  intro e heU
                  obtain ⟨a, ha, p, q, rfl, hpq, b_a, hreach, hgval, _, hside⟩ := hU_g e heU
                  have hwmax_pq : p ∈ wmax G D g ∨ q ∈ wmax G D g := by
                    rcases hside with hp | hq
                    · exact Or.inl (hSide_wmax a ha b_a hreach p hp)
                    · exact Or.inr (hSide_wmax a ha b_a hreach q hq)
                  rw [hg_iff] at hgval
                  rcases hgval with ⟨⟨p0, hp0, hp0_eq⟩, ⟨q1, hq1, hq1_eq⟩⟩
                  have hp0' : p0 = p ∨ p0 = q := by simpa [pairInput] using hp0_eq
                  have hq1' : q1 = p ∨ q1 = q := by simpa [pairInput] using hq1_eq
                  have hnot_out : ∀ z ∈ wmax G D g, ∀ y, s(z, y) = s(p, q) →
                      z ∈ S0 ∪ S1 := by
                    intro z hzw y hsy
                    by_contra hz_not
                    have hy_S0 : y ∈ S0 := by
                      rcases hp0' with rfl | rfl
                      · rcases Sym2.eq_iff.mp hsy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
                        · exact absurd (Finset.mem_union_left _ hp0) hz_not
                        · exact hp0
                      · rcases Sym2.eq_iff.mp hsy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
                        · exact hp0
                        · exact absurd (Finset.mem_union_left _ hp0) hz_not
                    have hy_S1 : y ∈ S1 := by
                      rcases hq1' with rfl | rfl
                      · rcases Sym2.eq_iff.mp hsy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
                        · exact absurd (Finset.mem_union_right _ hq1) hz_not
                        · exact hq1
                      · rcases Sym2.eq_iff.mp hsy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
                        · exact hq1
                        · exact absurd (Finset.mem_union_right _ hq1) hz_not
                    have hy_w : y = w := (hI_iff y).mp (Finset.mem_inter.mpr ⟨hy_S0, hy_S1⟩)
                    subst hy_w
                    have hz_in : z ∈ W_out := Finset.mem_filter.mpr
                      ⟨Finset.mem_sdiff.mpr ⟨hzw, hz_not⟩, by rw [Sym2.eq_swap, hsy]; exact heU⟩
                    rw [hWout] at hz_in
                    exact absurd hz_in (Finset.notMem_empty _)
                  rcases hwmax_pq with hpw | hqw
                  · have hp_S01 := hnot_out p hpw q rfl
                    rcases Finset.mem_union.mp hp_S01 with hpS0 | hpS1
                    · have hpW0 : p ∈ W0 := Finset.mem_filter.mpr ⟨hpw, hpS0⟩
                      have hpnS1 : p ∉ S1 := hW0_nS1 p hpW0
                      have hqS1 : q ∈ S1 := by
                        rcases hq1' with rfl | rfl
                        · exact absurd hq1 hpnS1
                        · exact hq1
                      exact ⟨p, hpS0, q, hqS1, rfl, hpq, Or.inl hpW0⟩
                    · have hpW1 : p ∈ W1 := Finset.mem_filter.mpr ⟨hpw, hpS1⟩
                      have hpnS0 : p ∉ S0 := hW1_nS0 p hpW1
                      have hqS0 : q ∈ S0 := by
                        rcases hp0' with rfl | rfl
                        · exact absurd hp0 hpnS0
                        · exact hp0
                      exact ⟨q, hqS0, p, hpS1, Sym2.eq_swap, hpq.symm, Or.inr hpW1⟩
                  · have hq_S01 := hnot_out q hqw p Sym2.eq_swap
                    rcases Finset.mem_union.mp hq_S01 with hqS0 | hqS1
                    · have hqW0 : q ∈ W0 := Finset.mem_filter.mpr ⟨hqw, hqS0⟩
                      have hqnS1 : q ∉ S1 := hW0_nS1 q hqW0
                      have hpS1 : p ∈ S1 := by
                        rcases hq1' with rfl | rfl
                        · exact hq1
                        · exact absurd hq1 hqnS1
                      exact ⟨q, hqS0, p, hpS1, Sym2.eq_swap, hpq.symm, Or.inl hqW0⟩
                    · have hqW1 : q ∈ W1 := Finset.mem_filter.mpr ⟨hqw, hqS1⟩
                      have hqnS0 : q ∉ S0 := hW1_nS0 q hqW1
                      have hpS0 : p ∈ S0 := by
                        rcases hp0' with rfl | rfl
                        · exact hp0
                        · exact absurd hp0 hqnS0
                      exact ⟨p, hpS0, q, hqS1, rfl, hpq, Or.inr hqW1⟩
                rcases hW01_empty with hW0e | hW1e
                · by_cases hS0_le1 : S0.card ≤ 1
                  · apply hOneCover w 1
                    intro e he
                    obtain ⟨u, hu, v, hv, rfl, huv, _⟩ := hU_W01 e he
                    have huw : u = w := Finset.card_le_one.mp hS0_le1 u hu w hw_S0
                    subst huw
                    exact ⟨Sym2.mem_mk_left _ _, v, hv, huv.symm, rfl⟩
                  · have hS0_ge2 : 2 ≤ S0.card := by omega
                    have hW1_le1 := hW1_card hS0_ge2
                    obtain ⟨e0, he0⟩ := hU
                    obtain ⟨_, _, v0, _, _, _, hw0⟩ := hU_W01 e0 he0
                    have hv0_W1 : v0 ∈ W1 := by
                      rcases hw0 with hu0 | hv0
                      · rw [hW0e] at hu0; exact absurd hu0 (Finset.notMem_empty _)
                      · exact hv0
                    apply hOneCover v0 0
                    intro e he
                    obtain ⟨u, hu, v, hv, rfl, huv, hw⟩ := hU_W01 e he
                    have hv_W1 : v ∈ W1 := by
                      rcases hw with huw | hvw
                      · rw [hW0e] at huw; exact absurd huw (Finset.notMem_empty _)
                      · exact hvw
                    have hvv0 : v = v0 := Finset.card_le_one.mp hW1_le1 v hv_W1 v0 hv0_W1
                    subst hvv0
                    exact ⟨Sym2.mem_mk_right _ _, u, hu, huv, Sym2.eq_swap⟩
                · by_cases hS1_le1 : S1.card ≤ 1
                  · apply hOneCover w 0
                    intro e he
                    obtain ⟨u, hu, v, hv, rfl, huv, _⟩ := hU_W01 e he
                    have hvw : v = w := Finset.card_le_one.mp hS1_le1 v hv w hw_S1
                    subst hvw
                    exact ⟨Sym2.mem_mk_right _ _, u, hu, huv, Sym2.eq_swap⟩
                  · have hS1_ge2 : 2 ≤ S1.card := by omega
                    have hW0_le1 := hW0_card hS1_ge2
                    obtain ⟨e0, he0⟩ := hU
                    obtain ⟨u0, _, _, _, _, _, hw0⟩ := hU_W01 e0 he0
                    have hu0_W0 : u0 ∈ W0 := by
                      rcases hw0 with hu0 | hv0
                      · exact hu0
                      · rw [hW1e] at hv0; exact absurd hv0 (Finset.notMem_empty _)
                    apply hOneCover u0 1
                    intro e he
                    obtain ⟨u, hu, v, hv, rfl, huv, hw⟩ := hU_W01 e he
                    have hu_W0 : u ∈ W0 := by
                      rcases hw with huw | hvw
                      · exact huw
                      · rw [hW1e] at hvw; exact absurd hvw (Finset.notMem_empty _)
                    have huu0 : u = u0 := Finset.card_le_one.mp hW0_le1 u hu_W0 u0 hu0_W0
                    subst huu0
                    exact ⟨Sym2.mem_mk_left _ _, v, hv, huv.symm, rfl⟩
              · -- When W_out.Nonempty, derive False from hDleast
                obtain ⟨wireVal_gs, hwire_gs_eq⟩ :
                    ∃ f : List Gate → ℕ → (Fin N → Bool) → Bool,
                      f = fun gs i x => (gs.foldl stepWire (List.ofFn x)).getD i false :=
                  ⟨_, rfl⟩
                have hwire_lt : ∀ (gs : List Gate) (i : ℕ) (hi : i < N) (x : Fin N → Bool),
                    wireVal_gs gs i x = x ⟨i, hi⟩ := by
                  intro gs i hi x
                  rw [hwire_gs_eq]; dsimp only
                  rw [foldl_getD_lt gs (List.ofFn x) i (by rw [List.length_ofFn]; exact hi),
                    List.getD_eq_getElem?_getD]
                  simp [hi]
                have hwire_gate : ∀ (gs : List Gate) (j : ℕ) (hj : j < gs.length) (x : Fin N → Bool),
                    wireVal_gs gs (N + j) x = (gs[j]'hj).op.eval
                      ((gs[j]'hj).inputs.map fun inp => if inp < N + j then wireVal_gs gs inp x else false) := by
                  intro gs j hj x
                  rw [hwire_gs_eq]; dsimp only
                  have h1 := foldl_getD_gate gs (List.ofFn x) j hj
                  rw [List.length_ofFn] at h1
                  exact h1
                let remapK : ℕ → ℕ → ℕ → ℕ := fun k0 r0 i =>
                  if i = N + k0 then r0 else if N + k0 < i then i - 1 else i
                let origK : ℕ → ℕ → ℕ := fun k0 i =>
                  if i < N + k0 then i else i + 1
                obtain ⟨eraseCircuit, herase_eq⟩ :
                    ∃ f : ℕ → ℕ → Circuit,
                      f = fun k0 r0 =>
                        Circuit.mk ((D.gates.eraseIdx k0).map (fun gt => Gate.mk gt.op (gt.inputs.map (remapK k0 r0))))
                          (remapK k0 r0 D.output) :=
                  ⟨_, rfl⟩
                have hremapK_eq : ∀ k0 r0, remapK k0 r0 (N + k0) = r0 := fun k0 r0 => by
                  dsimp [remapK]; exact if_pos rfl
                have hremapK_lt : ∀ k0 r0 i, i < N + k0 → remapK k0 r0 i = i := fun k0 r0 i h => by
                  dsimp [remapK]; rw [if_neg (Nat.ne_of_lt h), if_neg (Nat.not_lt_of_ge (Nat.le_of_lt h))]
                have hremapK_gt : ∀ k0 r0 i, N + k0 < i → remapK k0 r0 i = i - 1 := fun k0 r0 i h => by
                  dsimp [remapK]; rw [if_neg (Nat.ne_of_gt h), if_pos h]
                have horigK_lt : ∀ k0 i, i < N + k0 → origK k0 i = i := fun k0 i h => by
                  dsimp [origK]; exact if_pos h
                have horigK_ge : ∀ k0 i, N + k0 ≤ i → origK k0 i = i + 1 := fun k0 i h => by
                  dsimp [origK]; exact if_neg (Nat.not_lt_of_ge h)
                have hremapK_gate : ∀ k0 r0 k, k0 < D.gates.length → k < D.gates.length → k ≠ k0 →
                    ∃ j, remapK k0 r0 (N + k) = N + j ∧ j < D.gates.length - 1 ∧
                      (k = if j < k0 then j else j + 1) := by
                  intro k0 r0 k hk0 hk hne
                  rcases lt_or_ge k k0 with hlt | hge
                  · refine ⟨k, hremapK_lt k0 r0 (N + k) (Nat.add_lt_add_left hlt N), ?_, (if_pos hlt).symm⟩
                    omega
                  · have hgt : k0 < k := Nat.lt_of_le_of_ne hge hne.symm
                    refine ⟨k - 1, ?_, ?_, ?_⟩
                    · rw [hremapK_gt k0 r0 (N + k) (Nat.add_lt_add_left hgt N)]; omega
                    · omega
                    · rw [if_neg (by omega)]; omega
                have horigK_remap : ∀ k0 r0 i, i ≠ N + k0 → origK k0 (remapK k0 r0 i) = i := by
                  intro k0 r0 i hi
                  rcases lt_trichotomy i (N + k0) with hlt | heq | hgt
                  · dsimp [remapK, origK]; rw [if_neg (Nat.ne_of_lt hlt), if_neg (not_lt.mpr (le_of_lt hlt)), if_pos hlt]
                  · exact absurd heq hi
                  · dsimp [remapK, origK]; rw [if_neg (Nat.ne_of_gt hgt), if_pos hgt, if_neg (by omega)]; omega
                have hErase_len : ∀ k0 r0, k0 < D.gates.length →
                    (eraseCircuit k0 r0).gates.length = D.gates.length - 1 := by
                  intro k0 r0 hk0
                  rw [herase_eq]
                  simp only [List.length_map, List.length_eraseIdx_of_lt hk0]
                have hErase_get : ∀ k0 r0 (j k : ℕ) (hj : j < (eraseCircuit k0 r0).gates.length)
                    (hk : k < D.gates.length), k = (if j < k0 then j else j + 1) →
                    (eraseCircuit k0 r0).gates[j]'hj =
                      ⟨(D.gates[k]'hk).op, (D.gates[k]'hk).inputs.map (remapK k0 r0)⟩ := by
                  intro k0 r0 j k hj hk hjk
                  have hj' : j < ((D.gates.eraseIdx k0).map (fun gt => Gate.mk gt.op (gt.inputs.map (remapK k0 r0)))).length := by
                    simpa [herase_eq] using hj
                  have h1 : (eraseCircuit k0 r0).gates[j]'hj =
                      ((D.gates.eraseIdx k0).map (fun gt => Gate.mk gt.op (gt.inputs.map (remapK k0 r0))))[j]'hj' := by
                    congr 1; exact congrArg (fun f => (f k0 r0).gates) herase_eq
                  rw [h1]
                  simp only [List.getElem_map, List.getElem_eraseIdx]
                  by_cases hjg : j < k0
                  · have hkj : k = j := by rw [hjk, if_pos hjg]
                    subst hkj; simp [hjg]
                  · have hkj : k = j + 1 := by rw [hjk, if_neg hjg]
                    subst hkj; simp [hjg]
                have hErase_AO2 : ∀ k0 r0, k0 < D.gates.length → r0 < N →
                    IsAO2 N (eraseCircuit k0 r0) := by
                  intro k0 r0 hk0_len hr0
                  refine ⟨?_, ?_, ?_⟩
                  · intro gt hgt
                    rw [herase_eq] at hgt
                    simp only [List.mem_map] at hgt
                    obtain ⟨gt0, hgt0, rfl⟩ := hgt
                    exact hDAO.1 gt0 (List.mem_of_mem_eraseIdx hgt0)
                  · intro j hj inp hinp
                    have hj' : j < D.gates.length - 1 := by rwa [hErase_len k0 r0 hk0_len] at hj
                    obtain ⟨k, hk_lt, hjk⟩ : ∃ k, k < D.gates.length ∧ k = (if j < k0 then j else j + 1) := by
                      by_cases hjk : j < k0
                      · exact ⟨j, by omega, (if_pos hjk).symm⟩
                      · exact ⟨j + 1, by omega, (if_neg hjk).symm⟩
                    have hget := hErase_get k0 r0 j k hj hk_lt hjk
                    have hget_at : gateAt (eraseCircuit k0 r0) j = (eraseCircuit k0 r0).gates[j]'hj := by
                      unfold gateAt; simp [List.getD_eq_getElem?_getD, hj]
                    rw [hget_at, hget] at hinp
                    simp only [List.mem_map] at hinp
                    obtain ⟨inp0, hinp0, rfl⟩ := hinp
                    have hinp0_lt : inp0 < N + k := hDAO.2.1 k hk_lt inp0 (by rw [hgateAt_D k hk_lt]; exact hinp0)
                    by_cases heq : inp0 = N + k0
                    · rw [heq, hremapK_eq]; exact Nat.lt_of_lt_of_le hr0 (Nat.le_add_right N j)
                    · by_cases hlt : inp0 < N + k0
                      · rw [hremapK_lt k0 r0 inp0 hlt]
                        by_cases hjk' : j < k0
                        · rw [if_pos hjk'] at hjk; rw [hjk] at hinp0_lt; exact hinp0_lt
                        · rw [if_neg hjk'] at hjk; exact Nat.lt_of_lt_of_le hlt (by omega)
                      · have hgt : N + k0 < inp0 := Nat.lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm heq)
                        rw [hremapK_gt k0 r0 inp0 hgt]
                        by_cases hjk' : j < k0
                        · rw [if_pos hjk'] at hjk; rw [hjk] at hinp0_lt; omega
                        · rw [if_neg hjk'] at hjk; rw [hjk] at hinp0_lt; omega
                  · intro gt hgt
                    rw [herase_eq] at hgt
                    simp only [List.mem_map] at hgt
                    obtain ⟨gt0, hgt0, rfl⟩ := hgt
                    simp only [List.length_map]
                    exact hDAO.2.2 gt0 (List.mem_of_mem_eraseIdx hgt0)
                have hout_lt_D : D.output < N + D.gates.length := by
                  by_contra! hge
                  obtain ⟨e0, he0⟩ := hEdges
                  obtain ⟨d0, hd0, rfl⟩ := Finset.mem_image.mp (edgeFinset_eq ▸ he0)
                  have hd : circuitFun N D (pairInput (L d0.1) (R d0.2)) = true := by
                    rw [hDeval]; unfold graphFun
                    simp only [Finset.notMem_empty, false_and, exists_false, decide_false,
                      Bool.false_or, decide_eq_true_eq]
                    exact ⟨L d0.1, R d0.2, (incidence d0.1 d0.2).mpr hd0, by simp [pairInput], by simp [pairInput]⟩
                  have hlen : (D.gates.foldl stepWire (List.ofFn (pairInput (L d0.1) (R d0.2)))).length =
                      N + D.gates.length := by rw [foldl_length, List.length_ofFn]
                  have hf : circuitFun N D (pairInput (L d0.1) (R d0.2)) = false := by
                    change (D.gates.foldl stepWire (List.ofFn (pairInput (L d0.1) (R d0.2)))).getD D.output false = false
                    exact getD_ge _ _ (by omega)
                  rw [hd] at hf; cases hf
                let StepOut : ℕ → ℕ → Prop := fun i j =>
                  ∃ k < D.gates.length, i = N + k ∧ j ∈ (gateAt D k).inputs
                have hNoDead : ∀ k0 < D.gates.length,
                    Relation.ReflTransGen StepOut D.output (N + k0) := by
                  intro k0 hk0_len
                  by_contra hNotReach
                  have hout0_ne : D.output ≠ N + k0 := by
                    intro heq; apply hNotReach; rw [← heq]
                  obtain ⟨D0', hD0'_eq⟩ : ∃ x, x = eraseCircuit k0 0 := ⟨_, rfl⟩
                  have hD0'_len : D0'.gates.length = D.gates.length - 1 := by
                    rw [hD0'_eq]; exact hErase_len k0 0 hk0_len
                  have hD0'_AO2 : IsAO2 N D0' := by
                    rw [hD0'_eq]; exact hErase_AO2 k0 0 hk0_len (Fin.pos w)
                  have hAgreeReach : ∀ m, m < N + D0'.gates.length →
                      Relation.ReflTransGen StepOut D.output (origK k0 m) →
                      ∀ x : Fin N → Bool, wireVal_gs D0'.gates m x = wireVal (origK k0 m) x := by
                    intro m
                    induction m using Nat.strong_induction_on with
                    | ind m ih =>
                      intro hm hreach x
                      by_cases hmN : m < N
                      · have hm_orig : origK k0 m = m := horigK_lt k0 m (Nat.lt_of_lt_of_le hmN (Nat.le_add_right N k0))
                        rw [hm_orig, hwire_lt D0'.gates m hmN x, wireVal_lt ⟨m, hmN⟩ x]
                      · obtain ⟨j, hj_eq⟩ : ∃ j, m = N + j := ⟨m - N, by omega⟩
                        subst hj_eq
                        have hj : j < D0'.gates.length := Nat.lt_of_add_lt_add_left hm
                        have hj' : j < D.gates.length - 1 := by rwa [hD0'_len] at hj
                        obtain ⟨k, hk_lt, hNk, hjk⟩ : ∃ k, k < D.gates.length ∧ origK k0 (N + j) = N + k ∧ k = (if j < k0 then j else j + 1) := by
                          by_cases hjk0 : j < k0
                          · exact ⟨j, by omega, horigK_lt k0 (N + j) (Nat.add_lt_add_left hjk0 N), (if_pos hjk0).symm⟩
                          · exact ⟨j + 1, by omega, by rw [horigK_ge k0 (N + j) (Nat.add_le_add_left (not_lt.mp hjk0) N), Nat.add_assoc], (if_neg hjk0).symm⟩
                        have hget : D0'.gates[j]'hj = ⟨(D.gates[k]'hk_lt).op, (D.gates[k]'hk_lt).inputs.map (remapK k0 0)⟩ := by
                          have hj0 : j < (eraseCircuit k0 0).gates.length := by rwa [← hD0'_eq]
                          simpa only [← hD0'_eq] using hErase_get k0 0 j k hj0 hk_lt hjk
                        have hget_D := hgateAt_D k hk_lt
                        have hw0' := hwire_gate D0'.gates j hj x
                        rw [hget] at hw0'
                        have ha01 : (D.gates[k]'hk_lt).inputs = [opnd D k 0, opnd D k 1] := by
                          rw [← hget_D]; exact hgateAt_D_inputs k hk_lt
                        let a0 := opnd D k 0
                        let a1 := opnd D k 1
                        have ha0_lt : a0 < N + k := hopnd_D_lt k hk_lt 0
                        have ha1_lt : a1 < N + k := hopnd_D_lt k hk_lt 1
                        have hreach_inp : ∀ inp ∈ [a0, a1], Relation.ReflTransGen StepOut D.output inp := by
                          intro inp hinp
                          refine Relation.ReflTransGen.tail hreach ?_
                          exact ⟨k, hk_lt, hNk, by rw [hget_D, ha01]; exact hinp⟩
                        have hne_inp : ∀ inp ∈ [a0, a1], inp ≠ N + k0 := by
                          intro inp hinp heq; apply hNotReach; rw [← heq]; exact hreach_inp inp hinp
                        have hra_lt : ∀ inp, inp < N + k → inp ≠ N + k0 → remapK k0 0 inp < N + j := by
                          intro inp hinp hne
                          by_cases hlt : inp < N + k0
                          · rw [hremapK_lt k0 0 inp hlt]
                            by_cases hjk0 : j < k0
                            · rw [if_pos hjk0] at hjk; omega
                            · rw [if_neg hjk0] at hjk; omega
                          · have hgt : N + k0 < inp := Nat.lt_of_le_of_ne (not_lt.mp hlt) hne.symm
                            rw [hremapK_gt k0 0 inp hgt]
                            by_cases hjk0 : j < k0
                            · rw [if_pos hjk0] at hjk; omega
                            · rw [if_neg hjk0] at hjk; omega
                        have hra0_lt := hra_lt a0 ha0_lt (hne_inp a0 (by simp only [List.mem_cons, true_or]))
                        have hra1_lt := hra_lt a1 ha1_lt (hne_inp a1 (by simp only [List.mem_cons, List.mem_nil_iff, or_false, or_true]))
                        have hval_inp : ∀ inp ∈ [a0, a1],
                            wireVal_gs D0'.gates (remapK k0 0 inp) x = wireVal inp x := by
                          intro inp hinp
                          have hne := hne_inp inp hinp
                          have hlt_j : remapK k0 0 inp < N + j := by
                            rcases List.mem_cons.mp hinp with rfl | hmem
                            · exact hra0_lt
                            · rw [List.mem_singleton.mp hmem]; exact hra1_lt
                          have hih := ih (remapK k0 0 inp) hlt_j (Nat.lt_trans hlt_j hm)
                            (by rw [horigK_remap k0 0 inp hne]; exact hreach_inp inp hinp) x
                          rwa [horigK_remap k0 0 inp hne] at hih
                        have h0eq : opnd D k 0 = a0 := by unfold opnd; rw [hget_D, ha01]; rfl
                        have h1eq : opnd D k 1 = a1 := by unfold opnd; rw [hget_D, ha01]; rfl
                        rw [hw0', ha01, hNk, wireVal_gate k hk_lt x, h0eq, h1eq, hget_D]
                        simp only [List.map_cons, List.map_nil, hra0_lt, hra1_lt, ↓reduceIte]
                        rw [hval_inp a0 (by simp only [List.mem_cons, true_or]),
                          hval_inp a1 (by simp only [List.mem_cons, List.mem_nil_iff, or_false, or_true])]
                  have hD0'_eval : circuitFun N D0' = graphFun G ∅ := by
                    ext x
                    have hcf : circuitFun N D0' x = wireVal_gs D0'.gates (remapK k0 0 D.output) x := by
                      have hd0' : D0'.output = remapK k0 0 D.output := by rw [hD0'_eq, herase_eq]
                      rw [← hd0', hwire_gs_eq]; rfl
                    have hout0'_lt : remapK k0 0 D.output < N + D0'.gates.length := by
                      rw [hD0'_len]
                      by_cases hlt : D.output < N + k0
                      · rw [hremapK_lt k0 0 D.output hlt]; omega
                      · have hgt : N + k0 < D.output := Nat.lt_of_le_of_ne (not_lt.mp hlt) hout0_ne.symm
                        rw [hremapK_gt k0 0 D.output hgt]; omega
                    have hreach_out : Relation.ReflTransGen StepOut D.output (origK k0 (remapK k0 0 D.output)) := by
                      rw [horigK_remap k0 0 D.output hout0_ne]
                    rw [hcf, hAgreeReach (remapK k0 0 D.output) hout0'_lt hreach_out x,
                      horigK_remap k0 0 D.output hout0_ne]
                    exact congrFun hDeval x
                  have hle := hDleast.2.2 D0' hD0'_AO2 hD0'_eval
                  have hD0'_lt : D0'.size < D.size := by
                    change D0'.gates.length < D.gates.length; rw [hD0'_len]; omega
                  omega
                have hTop_orReaches_out : ∀ a ∈ tops G D, OrReaches N D D.output a := by
                  intro a ha
                  have ha' := ha
                  simp only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range] at ha'
                  have hpath := hNoDead a ha'.1
                  have hgen : ∀ i, Relation.ReflTransGen StepOut i (N + a) → OrReaches N D i a := by
                    intro i hi
                    induction hi using Relation.ReflTransGen.head_induction_on with
                    | refl => exact hOrReaches_self a ha'.1
                    | @head _ j_mid hstep _ ih =>
                      obtain ⟨k, hk_len, rfl, hj_mem⟩ := hstep
                      have hj_lt : j_mid < N + k := hDAO.2.1 k hk_len j_mid hj_mem
                      have hkop : (gateAt D k).op = GateOp.or := by
                        rcases hDAO.1 (gateAt D k) (by
                          unfold gateAt; simp [List.getD_eq_getElem?_getD, hk_len, List.getElem_mem]) with hand | hor
                        · exfalso
                          rcases hAnd_split k hk_len hand with htop | hjunk
                          · have hincone : InCone N D a k := by
                              rw [inCone_iff]
                              exact ⟨hk_len, j_mid, hj_mem, ih.1, hj_lt,
                                orReaches_inCone (j_mid - N) a (by
                                  have heq : N + (j_mid - N) = j_mid := by have := ih.1; omega
                                  rwa [heq])⟩
                            exact hDtop a ha'.1 k hk_len ha'.2.1 ha'.2.2 hand hincone
                          · rw [hg_eq, Finset.mem_singleton] at hjunk
                            subst hjunk
                            have hlen2 : (gateAt D k).inputs.length = 2 := by
                              apply hDAO.2.2; unfold gateAt; simp [List.getD_eq_getElem?_getD, hk_len]
                            obtain ⟨idx, hidx, hidx_eq⟩ := List.mem_iff_getElem.mp hj_mem
                            have hidx2 : idx < 2 := by omega
                            let b : Fin 2 := ⟨idx, hidx2⟩
                            have hb_eq : opnd D k b = j_mid := by
                              unfold opnd; simp [b, List.getD_eq_getElem?_getD, hidx, hidx_eq]
                            rw [← hb_eq] at ih
                            exact hNoAnd_g b ⟨a, ha'.1, ha'.2.1, ih⟩
                        · exact hor
                      exact hOrReaches_step (N + k) k a (hOrReaches_self k hk_len) hkop j_mid hj_mem hj_lt ih
                  exact hgen D.output hpath
                have hDelete_contra :
                    (∀ u ∈ W0, ∀ v ∈ S1 \ {w}, s(u, v) ∉ Ustar G D) →
                    (∀ v ∈ W1, ∀ u ∈ S0 \ {w}, s(u, v) ∉ Ustar G D) → False := by
                  intro hNoW0 hNoW1
                  clear charge compileStars h4 hc hDtop hDsize hmin hLeast orSets_len orSets_char hGML hj2 cones_char hOneCover hNoDead hNo4 hcard hW0_adj_S1 hW1_adj_S0
                  let remap := remapK g w.1
                  let orig := origK g
                  have hremap_lt : ∀ i, i < N + g → remap i = i := by
                    intro i hi; dsimp [remap, remapK]; rw [if_neg (Nat.ne_of_lt hi), if_neg (not_lt.mpr (le_of_lt hi))]
                  have hremap_gt : ∀ i, N + g < i → remap i = i - 1 := by
                    intro i hi; dsimp [remap, remapK]; rw [if_neg (Nat.ne_of_gt hi), if_pos hi]
                  have hremap_eq : remap (N + g) = w.1 := by dsimp [remap, remapK]; rw [if_pos rfl]
                  have horig_remap : ∀ i, i ≠ N + g → orig (remap i) = i := horigK_remap g w.1
                  have hremap_orig : ∀ j, j ≠ w.1 → remap (orig j) = j := by
                    intro j _
                    by_cases hlt : j < N + g
                    · dsimp [orig, origK]; rw [if_pos hlt]; exact hremap_lt j hlt
                    · dsimp [orig, origK]; rw [if_neg hlt]; rw [hremap_gt (j + 1) (by omega)]; omega
                  have hout_ne : D.output ≠ N + g := by
                    intro heq
                    apply hg_nbel
                    intro x hx
                    have hfun : circuitFun N D x = true := by
                      change wireVal D.output x = true
                      rw [heq]; rwa [← gateVal_eq_wireVal]
                    rwa [hDeval] at hfun
                  have hout_lt : D.output < N + D.gates.length := hout_lt_D
                  obtain ⟨D', hD'_eq⟩ : ∃ x, x = eraseCircuit g w.1 := ⟨_, rfl⟩
                  have hD'_len : D'.gates.length = D.gates.length - 1 := by
                    rw [hD'_eq]; exact hErase_len g w.1 hg_len
                  have hD'_lt : D'.size < D.size := by
                    change D'.gates.length < D.gates.length; rw [hD'_len]; omega
                  have hout'_eq : D'.output = remap D.output := by
                    rw [hD'_eq, herase_eq]
                  have hout'_lt_remap : remap D.output < N + D'.gates.length := by
                    rw [hD'_len]
                    by_cases hlt : D.output < N + g
                    · rw [hremap_lt D.output hlt]; omega
                    · have hgt : N + g < D.output := by omega
                      rw [hremap_gt D.output hgt]; omega
                  have hout'_lt : D'.output < N + D'.gates.length := by
                    rw [hout'_eq]; exact hout'_lt_remap
                  have hD'_get : ∀ (j k : ℕ) (hj : j < D'.gates.length) (hk : k < D.gates.length),
                      k = (if j < g then j else j + 1) →
                      D'.gates[j]'hj = ⟨(D.gates[k]'hk).op, (D.gates[k]'hk).inputs.map remap⟩ := by
                    intro j k hj hk hjk
                    have hj' : j < (eraseCircuit g w.1).gates.length := by rwa [← hD'_eq]
                    have h := hErase_get g w.1 j k hj' hk hjk
                    simpa only [← hD'_eq] using h
                  have hD'_AO2 : IsAO2 N D' := by
                    rw [hD'_eq]; exact hErase_AO2 g w.1 hg_len w.isLt
                  obtain ⟨wireVal', hwire'_eq⟩ : ∃ x, x = wireVal_gs D'.gates := ⟨_, rfl⟩
                  have wireVal'_lt : ∀ i (hi : i < N) x, wireVal' i x = x ⟨i, hi⟩ := by
                    rw [hwire'_eq]; exact hwire_lt D'.gates
                  have wireVal'_gate : ∀ j (hj : j < D'.gates.length) x,
                      wireVal' (N + j) x = (D'.gates[j]'hj).op.eval
                        ((D'.gates[j]'hj).inputs.map fun i => if i < N + j then wireVal' i x else false) := by
                    rw [hwire'_eq]; exact hwire_gate D'.gates
                  have horig_gate : ∀ j, j < D'.gates.length →
                      ∃ k, k < D.gates.length ∧ orig (N + j) = N + k ∧ k = (if j < g then j else j + 1) := by
                    intro j hj
                    have hj' : j < D.gates.length - 1 := by rwa [hD'_len] at hj
                    by_cases hjg : j < g
                    · refine ⟨j, by omega, ?_, (if_pos hjg).symm⟩
                      exact horigK_lt g (N + j) (Nat.add_lt_add_left hjg N)
                    · refine ⟨j + 1, by omega, ?_, (if_neg hjg).symm⟩
                      dsimp [orig]
                      rw [horigK_ge g (N + j) (Nat.add_le_add_left (not_lt.mp hjg) N), Nat.add_assoc]
                  have hMono : ∀ i, i < N + D'.gates.length → ∀ x,
                      wireVal' i x = true → wireVal (orig i) x = true := by
                    intro i
                    induction i using Nat.strong_induction_on with
                    | ind i ih =>
                      intro hi x hval
                      by_cases hiN : i < N
                      · have horig : orig i = i := horigK_lt g i (Nat.lt_of_lt_of_le hiN (Nat.le_add_right N g))
                        rw [horig, wireVal_lt ⟨i, hiN⟩ x]
                        rwa [wireVal'_lt i hiN x] at hval
                      · obtain ⟨j, rfl⟩ : ∃ j, i = N + j := ⟨i - N, by omega⟩
                        have hj : j < D'.gates.length := Nat.lt_of_add_lt_add_left hi
                        obtain ⟨k, hk_lt, hNk, hjk⟩ := horig_gate j hj
                        rw [hNk]
                        have hget := hD'_get j k hj hk_lt hjk
                        rw [wireVal'_gate j hj x, hget] at hval
                        rw [wireVal_gate k hk_lt x]
                        have hget_D := hgateAt_D k hk_lt
                        let a0 := opnd D k 0
                        let a1 := opnd D k 1
                        have ha01 : (D.gates[k]'hk_lt).inputs = [a0, a1] := by
                          rw [← hget_D]; exact hgateAt_D_inputs k hk_lt
                        have ha0_eq : opnd D k 0 = a0 := rfl
                        have ha1_eq : opnd D k 1 = a1 := rfl
                        have ha0_lt : a0 < N + k := hopnd_D_lt k hk_lt 0
                        have ha1_lt : a1 < N + k := hopnd_D_lt k hk_lt 1
                        have hgat' : gateAt D' j = D'.gates[j]'hj := by
                          unfold gateAt; simp [List.getD_eq_getElem?_getD, hj]
                        have hra0_lt : remap a0 < N + j :=
                          hD'_AO2.2.1 j hj (remap a0) (by rw [hgat', hget, ha01]; exact List.mem_map_of_mem (by simp only [List.mem_cons, true_or]))
                        have hra1_lt : remap a1 < N + j :=
                          hD'_AO2.2.1 j hj (remap a1) (by rw [hgat', hget, ha01]; exact List.mem_map_of_mem (by simp only [List.mem_cons, List.mem_nil_iff, or_false, or_true]))
                        have hsub_val : ∀ a, a < N + k → remap a < N + j →
                            wireVal' (remap a) x = true → wireVal a x = true := by
                          intro a _ hra hwa
                          by_cases hag : a = N + g
                          · subst hag
                            rw [hremap_eq, wireVal'_lt w.1 w.isLt x] at hwa
                            rw [Fin.eta] at hwa
                            rw [hg_iff]
                            exact ⟨⟨w, hw_S0, hwa⟩, ⟨w, hw_S1, hwa⟩⟩
                          · have := ih (remap a) hra (by omega) x hwa
                            rwa [horig_remap a hag] at this
                        rw [ha01] at hval
                        rw [hget_D, ha0_eq, ha1_eq]
                        simp only [List.map_cons, List.map_nil, hra0_lt, hra1_lt, ↓reduceIte] at hval
                        rcases hDAO.1 (D.gates[k]'hk_lt) (List.getElem_mem _) with hop | hop
                        · rw [hop] at hval ⊢
                          simp only [GateOp.eval, List.all_cons, List.all_nil, Bool.and_true,
                            Bool.and_eq_true] at hval ⊢
                          exact ⟨hsub_val a0 ha0_lt hra0_lt hval.1,
                            hsub_val a1 ha1_lt hra1_lt hval.2⟩
                        · rw [hop] at hval ⊢
                          simp only [GateOp.eval, List.any_cons, List.any_nil, Bool.or_false,
                            Bool.or_eq_true] at hval ⊢
                          rcases hval with h0 | h1
                          · exact Or.inl (hsub_val a0 ha0_lt hra0_lt h0)
                          · exact Or.inr (hsub_val a1 ha1_lt hra1_lt h1)
                  have hAgreeW : ∀ i, i < N + D'.gates.length → ∀ x, x w = true →
                      wireVal' i x = wireVal (orig i) x := by
                    intro i
                    induction i using Nat.strong_induction_on with
                    | ind i ih =>
                      intro hi x hxw
                      by_cases hiN : i < N
                      · have horig : orig i = i := horigK_lt g i (Nat.lt_of_lt_of_le hiN (Nat.le_add_right N g))
                        rw [horig]
                        have h1 := wireVal'_lt i hiN x
                        have h2 := wireVal_lt ⟨i, hiN⟩ x
                        exact h1.trans h2.symm
                      · obtain ⟨j, rfl⟩ : ∃ j, i = N + j := ⟨i - N, by omega⟩
                        have hj : j < D'.gates.length := Nat.lt_of_add_lt_add_left hi
                        obtain ⟨k, hk_lt, hNk, hjk⟩ := horig_gate j hj
                        rw [hNk]
                        have hget := hD'_get j k hj hk_lt hjk
                        have hget_D := hgateAt_D k hk_lt
                        rw [wireVal'_gate j hj x, hget, wireVal_gate k hk_lt x, hget_D]
                        simp only [opnd]
                        let a0 := opnd D k 0
                        let a1 := opnd D k 1
                        have ha01 : (D.gates[k]'hk_lt).inputs = [a0, a1] := by
                          rw [← hget_D]; exact hgateAt_D_inputs k hk_lt
                        have ha0_lt : a0 < N + k := hopnd_D_lt k hk_lt 0
                        have ha1_lt : a1 < N + k := hopnd_D_lt k hk_lt 1
                        have hgat' : gateAt D' j = D'.gates[j]'hj := by
                          unfold gateAt; simp [List.getD_eq_getElem?_getD, hj]
                        have hra0_lt : remap a0 < N + j :=
                          hD'_AO2.2.1 j hj (remap a0) (by rw [hgat', hget, ha01]; exact List.mem_map_of_mem (by simp only [List.mem_cons, true_or]))
                        have hra1_lt : remap a1 < N + j :=
                          hD'_AO2.2.1 j hj (remap a1) (by rw [hgat', hget, ha01]; exact List.mem_map_of_mem (by simp only [List.mem_cons, List.mem_nil_iff, or_false, or_true]))
                        rw [ha01]
                        simp only [List.map_cons, List.map_nil, hra0_lt, hra1_lt, ↓reduceIte]
                        congr 1
                        have hval_inp : ∀ inp, inp ∈ [a0, a1] →
                            wireVal' (remap inp) x = wireVal inp x := by
                          intro inp hinp
                          have hinp_lt : inp < N + k := hDAO.2.1 k hk_lt inp (by
                            rw [hget_D, ha01]; exact hinp)
                          have hrinp_lt : remap inp < N + j :=
                            hD'_AO2.2.1 j hj (remap inp) (by rw [hgat', hget, ha01]; exact List.mem_map_of_mem hinp)
                          by_cases heq : inp = N + g
                          · subst heq
                            rw [hremap_eq, wireVal'_lt w.1 w.isLt x, Fin.eta, hxw]
                            symm; rw [hg_iff]
                            exact ⟨⟨w, hw_S0, hxw⟩, ⟨w, hw_S1, hxw⟩⟩
                          · have h1 := ih (remap inp) hrinp_lt (by omega) x hxw
                            rwa [horig_remap inp heq] at h1
                        have h0eq : (gateAt D k).inputs.getD (0 : Fin 2).val 0 = a0 := by rw [hget_D, ha01]; rfl
                        have h1eq : (gateAt D k).inputs.getD (1 : Fin 2).val 0 = a1 := by rw [hget_D, ha01]; rfl
                        rw [h0eq, h1eq, hval_inp a0 (by simp only [List.mem_cons, true_or]),
                          hval_inp a1 (by simp only [List.mem_cons, List.mem_nil_iff, or_false, or_true])]
                  have hOrIn_D' : ∀ i, i < N + D.gates.length → ∀ u ∈ orIn N D i,
                      ∀ x : Fin N → Bool, x u = true → wireVal' (remap i) x = true := by
                    intro i
                    induction i using Nat.strong_induction_on with
                    | ind i ih =>
                      intro hi u hu x hxu
                      by_cases hiN : i < N
                      · have hu_eq : i = u.1 := by
                          rw [orIn_iff_reach] at hu
                          rcases Relation.ReflTransGen.cases_head hu with h | ⟨d, hd, _⟩
                          · exact h
                          · obtain ⟨k, _, h3, _⟩ := hd; omega
                        rw [hremap_lt i (by omega), hu_eq, wireVal'_lt u.1 u.isLt x, Fin.eta]
                        exact hxu
                      · obtain ⟨k, rfl⟩ : ∃ k, i = N + k := ⟨i - N, by omega⟩
                        have hk_lt : k < D.gates.length := by omega
                        obtain ⟨_, hkop, inp, hinp_mem, hinp_lt, hu_inp⟩ := (hOrIn_gate k u).mp hu
                        have hk_ne : k ≠ g := by intro heq; subst heq; rw [hg_op] at hkop; cases hkop
                        obtain ⟨j, hjk, hj'_lt, hk_if⟩ := hremapK_gate g w.1 k hg_len hk_lt hk_ne
                        have hj_lt : j < D'.gates.length := by rwa [hD'_len]
                        have hget := hD'_get j k hj_lt hk_lt hk_if
                        have hget_D := hgateAt_D k hk_lt
                        dsimp [remap]; rw [hjk, wireVal'_gate j hj_lt x, hget, ← hget_D, hkop]
                        let a0 := opnd D k 0
                        let a1 := opnd D k 1
                        have ha01 : (D.gates[k]'hk_lt).inputs = [a0, a1] := by
                          rw [← hget_D]; exact hgateAt_D_inputs k hk_lt
                        have hgat' : gateAt D' j = D'.gates[j]'hj_lt := by
                          unfold gateAt; simp [List.getD_eq_getElem?_getD, hj_lt]
                        have hra0_lt : remap a0 < N + j :=
                          hD'_AO2.2.1 j hj_lt (remap a0) (by rw [hgat', hget, ha01]; exact List.mem_map_of_mem (by simp only [List.mem_cons, true_or]))
                        have hra1_lt : remap a1 < N + j :=
                          hD'_AO2.2.1 j hj_lt (remap a1) (by rw [hgat', hget, ha01]; exact List.mem_map_of_mem (by simp only [List.mem_cons, List.mem_nil_iff, or_false, or_true]))
                        rw [hget_D, ha01]
                        simp only [List.map_cons, List.map_nil, hra0_lt, hra1_lt, ↓reduceIte,
                          GateOp.eval, List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true]
                        have hrec := ih inp hinp_lt (by omega) u hu_inp x hxu
                        rw [hget_D, ha01] at hinp_mem
                        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hinp_mem
                        rcases hinp_mem with h | h
                        · exact Or.inl (by rw [← h]; exact hrec)
                        · exact Or.inr (by rw [← h]; exact hrec)
                  have hOrIn_or_and : ∀ i, i < N + D.gates.length →
                      (∀ g' < D.gates.length, (gateAt D g').op = GateOp.and → OrReaches N D i g' → g' = g) →
                      ∀ x : Fin N → Bool, wireVal i x = true →
                      (∃ u ∈ orIn N D i, x u = true) ∨ wireVal (N + g) x = true := by
                    intro i
                    induction i using Nat.strong_induction_on with
                    | ind i ih =>
                      intro hi honly x hval
                      by_cases hiN : i < N
                      · left
                        refine ⟨⟨i, hiN⟩, ?_, ?_⟩
                        · rw [orIn_iff_reach]
                        · rwa [wireVal_lt ⟨i, hiN⟩ x] at hval
                      · obtain ⟨k, rfl⟩ : ∃ k, i = N + k := ⟨i - N, by omega⟩
                        have hk_lt : k < D.gates.length := by omega
                        rcases hDAO.1 (D.gates[k]'hk_lt) (List.getElem_mem _) with hop | hop
                        · have hkop : (gateAt D k).op = GateOp.and := by
                            unfold gateAt; simp [List.getD_eq_getElem?_getD, hk_lt, hop]
                          have hkeq : k = g := honly k hk_lt hkop (hOrReaches_self k hk_lt)
                          subst hkeq; exact Or.inr hval
                        · have hkop : (gateAt D k).op = GateOp.or := by
                            unfold gateAt; simp [List.getD_eq_getElem?_getD, hk_lt, hop]
                          rw [wireVal_gate_or k hk_lt hkop x] at hval
                          have hsub : ∀ b : Fin 2, opnd D k b < N + k ∧
                              (∀ g' < D.gates.length, (gateAt D g').op = GateOp.and →
                                OrReaches N D (opnd D k b) g' → g' = g) := by
                            intro b
                            have hlen2 : (gateAt D k).inputs.length = 2 := by
                              apply hDAO.2.2; unfold gateAt; simp [List.getD_eq_getElem?_getD, hk_lt]
                            have hmem : opnd D k b ∈ (gateAt D k).inputs := by
                              unfold opnd
                              have hb : (b : ℕ) < (gateAt D k).inputs.length := by omega
                              simp [hb, List.getElem_mem]
                            have hlt := hDAO.2.1 k hk_lt (opnd D k b) hmem
                            refine ⟨hlt, fun g' hg'len hg'op hreach' => honly g' hg'len hg'op ?_⟩
                            exact hOrReaches_step (N + k) k g' (hOrReaches_self k hk_lt) hkop _ hmem hlt hreach'
                          rcases hval with h0 | h1
                          · rcases ih (opnd D k 0) (hsub 0).1 (Nat.lt_trans (hsub 0).1 (by omega)) (hsub 0).2 x h0 with ⟨u, hu, hxu⟩ | hg_t
                            · left; refine ⟨u, ?_, hxu⟩
                              rw [hOrIn_gate]
                              have hlen2 : (gateAt D k).inputs.length = 2 := by
                                apply hDAO.2.2; unfold gateAt; simp [List.getD_eq_getElem?_getD, hk_lt]
                              exact ⟨hk_lt, hkop, opnd D k 0, by unfold opnd; simp [List.getD_eq_getElem?_getD, hlen2, List.getElem_mem],
                                (hsub 0).1, hu⟩
                            · exact Or.inr hg_t
                          · rcases ih (opnd D k 1) (hsub 1).1 (Nat.lt_trans (hsub 1).1 (by omega)) (hsub 1).2 x h1 with ⟨u, hu, hxu⟩ | hg_t
                            · left; refine ⟨u, ?_, hxu⟩
                              rw [hOrIn_gate]
                              have hlen2 : (gateAt D k).inputs.length = 2 := by
                                apply hDAO.2.2; unfold gateAt; simp [List.getD_eq_getElem?_getD, hk_lt]
                              exact ⟨hk_lt, hkop, opnd D k 1, by unfold opnd; simp [List.getD_eq_getElem?_getD, hlen2, List.getElem_mem],
                                (hsub 1).1, hu⟩
                            · exact Or.inr hg_t
                  have hAgreeNoG : ∀ x : Fin N → Bool,
                      (∀ a ∈ tops G D, ∀ b_a : Fin 2, OrReaches N D (opnd D a b_a) g →
                        wireVal (N + a) x = true → ∃ u ∈ PEqualNP.TopForm.side D a b_a, x u = true) →
                      ∀ i, i < N + D.gates.length → i ≠ N + g →
                        (∀ x', wireVal i x' = true → graphFun G ∅ x' = true) →
                        wireVal i x = true → wireVal' (remap i) x = true := by
                    intro x hNoTop i
                    induction i using Nat.strong_induction_on with
                    | ind i ih =>
                      intro hi hne hbel hval
                      by_cases hiN : i < N
                      · rw [hremap_lt i (by omega), wireVal'_lt i hiN x]
                        rwa [wireVal_lt ⟨i, hiN⟩ x] at hval
                      · obtain ⟨k, rfl⟩ : ∃ k, i = N + k := ⟨i - N, (Nat.add_sub_cancel' (Nat.le_of_not_lt hiN)).symm⟩
                        have hk_lt : k < D.gates.length := Nat.lt_of_add_lt_add_left hi
                        have hk_ne : k ≠ g := fun h => hne (congrArg (N + ·) h)
                        obtain ⟨j, hjk, hj_lt, hj_if⟩ := hremapK_gate g w.1 k hg_len hk_lt hk_ne
                        rw [← hD'_len] at hj_lt
                        have hget := hD'_get j k hj_lt hk_lt hj_if
                        have hget_D : gateAt D k = D.gates[k]'hk_lt := by
                          unfold gateAt; simp [List.getD_eq_getElem?_getD, hk_lt]
                        rcases hDAO.1 (D.gates[k]'hk_lt) (List.getElem_mem _) with hop | hop
                        · have hk_top : k ∈ tops G D := by
                            simp only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range]
                            refine ⟨hk_lt, ?_, ?_⟩
                            · rw [hget_D, hop]
                            · intro x' hx'; apply hbel x'; rwa [← gateVal_eq_wireVal]
                          have hget_side : ∀ b : Fin 2, ∃ u ∈ orIn N D (opnd D k b), x u = true := by
                            intro b
                            by_cases hreach_g : OrReaches N D (opnd D k b) g
                            · have h_ := hNoTop k hk_top b hreach_g hval
                              fin_cases b <;> exact h_
                            · have hNoAnd_kb : ¬ ∃ g' < D.gates.length,
                                  (gateAt D g').op = GateOp.and ∧ OrReaches N D (opnd D k b) g' := by
                                intro ⟨g', hg'len, hg'op, hreach'⟩
                                rcases hAnd_split g' hg'len hg'op with htop' | hjunk'
                                · exact hTop_not_in_cone k hk_top b g' hreach' htop'
                                · rw [hg_eq, Finset.mem_singleton] at hjunk'; subst hjunk'
                                  exact hreach_g hreach'
                              have hkop' : (gateAt D k).op = GateOp.and := by rw [hget_D, hop]
                              have hval' := (wireVal_gate_and k hk_lt hkop' x).mp hval
                              have hb_val : wireVal (opnd D k b) x = true := by
                                fin_cases b <;> [exact hval'.1; exact hval'.2]
                              exact (wireVal_orIn_iff_no_and (opnd D k b) x hNoAnd_kb).mp hb_val
                          obtain ⟨u0, hu0, hxu0⟩ := hget_side 0
                          obtain ⟨u1, hu1, hxu1⟩ := hget_side 1
                          let a0 := opnd D k 0
                          let a1 := opnd D k 1
                          have ha01 : (D.gates[k]'hk_lt).inputs = [a0, a1] := by
                            rw [← hget_D]; exact hgateAt_D_inputs k hk_lt
                          have h0eq : opnd D k 0 = a0 := rfl
                          have h1eq : opnd D k 1 = a1 := rfl
                          have hopnd0_lt : opnd D k 0 < N + k := hopnd_D_lt k hk_lt 0
                          have hopnd1_lt : opnd D k 1 < N + k := hopnd_D_lt k hk_lt 1
                          have hp0 := hOrIn_D' (opnd D k 0) (Nat.lt_trans hopnd0_lt hi) u0 hu0 x hxu0
                          have hp1 := hOrIn_D' (opnd D k 1) (Nat.lt_trans hopnd1_lt hi) u1 hu1 x hxu1
                          have hgat' : gateAt D' j = D'.gates[j]'hj_lt := by
                            unfold gateAt; simp [List.getD_eq_getElem?_getD, hj_lt]
                          have hra0_lt : remap (opnd D k 0) < N + j :=
                            hD'_AO2.2.1 j hj_lt (remap (opnd D k 0)) (by
                              rw [hgat', hget, ha01, h0eq]; exact List.mem_map_of_mem (by simp only [List.mem_cons, true_or]))
                          have hra1_lt : remap (opnd D k 1) < N + j :=
                            hD'_AO2.2.1 j hj_lt (remap (opnd D k 1)) (by
                              rw [hgat', hget, ha01, h1eq]; exact List.mem_map_of_mem (by simp only [List.mem_cons, List.mem_nil_iff, or_false, or_true]))
                          dsimp [remap]
                          rw [hjk, wireVal'_gate j hj_lt x, hget, hop, ha01, ← h0eq, ← h1eq]
                          simp only [List.map_cons, List.map_nil, hra0_lt, hra1_lt, ↓reduceIte,
                            GateOp.eval, List.all_cons, List.all_nil, Bool.and_true, hp0, hp1]
                          rfl
                        · let a0 := opnd D k 0
                          let a1 := opnd D k 1
                          have ha01 : (D.gates[k]'hk_lt).inputs = [a0, a1] := by
                            rw [← hget_D]; exact hgateAt_D_inputs k hk_lt
                          have h0eq : opnd D k 0 = a0 := rfl
                          have h1eq : opnd D k 1 = a1 := rfl
                          have ha0_lt : a0 < N + k := hopnd_D_lt k hk_lt 0
                          have ha1_lt : a1 < N + k := hopnd_D_lt k hk_lt 1
                          have hgat' : gateAt D' j = D'.gates[j]'hj_lt := by
                            unfold gateAt; simp [List.getD_eq_getElem?_getD, hj_lt]
                          have hra0_lt : remap a0 < N + j :=
                            hD'_AO2.2.1 j hj_lt (remap a0) (by rw [hgat', hget, ha01]; exact List.mem_map_of_mem (by simp only [List.mem_cons, true_or]))
                          have hra1_lt : remap a1 < N + j :=
                            hD'_AO2.2.1 j hj_lt (remap a1) (by rw [hgat', hget, ha01]; exact List.mem_map_of_mem (by simp only [List.mem_cons, List.mem_nil_iff, or_false, or_true]))
                          rw [wireVal_gate k hk_lt x, hget_D, hop, h0eq, h1eq] at hval
                          simp only [GateOp.eval, List.any_cons, List.any_nil, Bool.or_false,
                            Bool.or_eq_true] at hval
                          have ha0_bel : ∀ x', wireVal a0 x' = true → graphFun G ∅ x' = true := by
                            intro x' hx'; apply hbel x'
                            rw [wireVal_gate k hk_lt x', hget_D, hop, h0eq, h1eq]
                            simp only [GateOp.eval, List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true]
                            exact Or.inl hx'
                          have ha1_bel : ∀ x', wireVal a1 x' = true → graphFun G ∅ x' = true := by
                            intro x' hx'; apply hbel x'
                            rw [wireVal_gate k hk_lt x', hget_D, hop, h0eq, h1eq]
                            simp only [GateOp.eval, List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true]
                            exact Or.inr hx'
                          have ha0_ne : a0 ≠ N + g := by
                            intro heq; apply hg_nbel; intro x' hx'
                            exact ha0_bel x' (by rw [heq]; rwa [← gateVal_eq_wireVal])
                          have ha1_ne : a1 ≠ N + g := by
                            intro heq; apply hg_nbel; intro x' hx'
                            exact ha1_bel x' (by rw [heq]; rwa [← gateVal_eq_wireVal])
                          dsimp [remap]
                          rw [hjk, wireVal'_gate j hj_lt x, hget, hop, ha01]
                          simp only [List.map_cons, List.map_nil, hra0_lt, hra1_lt, ↓reduceIte,
                            GateOp.eval, List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true]
                          rcases hval with h0 | h1
                          · exact Or.inl (ih a0 ha0_lt (by omega) ha0_ne ha0_bel h0)
                          · exact Or.inr (ih a1 ha1_lt (by omega) ha1_ne ha1_bel h1)
                  have hD'_eval : circuitFun N D' = graphFun G ∅ := by
                    ext x
                    rw [Bool.eq_iff_iff]
                    have hcf : circuitFun N D' x = wireVal' (remap D.output) x := by
                      rw [hwire'_eq, ← hout'_eq, hwire_gs_eq]; rfl
                    rw [hcf]
                    constructor
                    · intro hval
                      have hlt : remap D.output < N + D'.gates.length := hout'_lt_remap
                      have hm := hMono (remap D.output) hlt x hval
                      rw [horig_remap D.output hout_ne] at hm
                      have hd : circuitFun N D x = true := hm
                      rwa [hDeval] at hd
                    · intro hgf
                      have hgf' := hgf
                      unfold graphFun at hgf'
                      simp only [Finset.notMem_empty, false_and, exists_false, decide_false,
                        Bool.false_or, decide_eq_true_eq] at hgf'
                      obtain ⟨u, v, hadj, hxu, hxv⟩ := hgf'
                      have hpair_gf : graphFun G ∅ (pairInput u v) = true := by
                        unfold graphFun
                        simp only [Finset.notMem_empty, false_and, exists_false, decide_false,
                          Bool.false_or, decide_eq_true_eq]
                        exact ⟨u, v, hadj, by simp only [pairInput, Bool.or_eq_true, decide_eq_true_eq, true_or],
                          by simp only [pairInput, Bool.or_eq_true, decide_eq_true_eq, or_true]⟩
                      have hpair_D : wireVal D.output (pairInput u v) = true := by
                        change circuitFun N D (pairInput u v) = true
                        rw [hDeval]; exact hpair_gf
                      have hpair_D' : wireVal' (remap D.output) (pairInput u v) = true := by
                        by_cases hw_uv : u = w ∨ v = w
                        · have hxw : pairInput u v w = true := by
                            rcases hw_uv with rfl | rfl <;>
                              simp only [pairInput, Bool.or_eq_true, decide_eq_true_eq, true_or, or_true]
                          have hlt : remap D.output < N + D'.gates.length := hout'_lt_remap
                          rw [hAgreeW (remap D.output) hlt (pairInput u v) hxw,
                            horig_remap D.output hout_ne]
                          exact hpair_D
                        · push Not at hw_uv
                          by_cases hU_uv : s(u, v) ∈ Ustar G D
                          · refine hAgreeNoG (pairInput u v) ?_ D.output hout_lt hout_ne ?_ hpair_D
                            · intro a ha b_a hreach ha_val
                              have ha' := ha
                              simp only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range] at ha'
                              have h_and := (wireVal_gate_and a ha'.1 ha'.2.1 (pairInput u v)).mp ha_val
                              have hba_val : wireVal (opnd D a b_a) (pairInput u v) = true := by
                                fin_cases b_a <;> [exact h_and.1; exact h_and.2]
                              have hopnd_lt : opnd D a b_a < N + a := hopnd_D_lt a ha'.1 b_a
                              have honly : ∀ g' < D.gates.length, (gateAt D g').op = GateOp.and →
                                  OrReaches N D (opnd D a b_a) g' → g' = g := by
                                intro g' hg'len hg'op hreach'
                                rcases hAnd_split g' hg'len hg'op with htop' | hjunk'
                                · exact False.elim (hTop_not_in_cone a ha b_a g' hreach' htop')
                                · rw [hg_eq, Finset.mem_singleton] at hjunk'; exact hjunk'
                              rcases hOrIn_or_and (opnd D a b_a) (by omega) honly (pairInput u v) hba_val with
                                ⟨x0, hx0, hxx0⟩ | hg_val
                              · refine ⟨x0, ?_, hxx0⟩
                                fin_cases b_a <;> exact hx0
                              · exfalso
                                rw [hg_iff] at hg_val
                                rcases hg_val with ⟨⟨p0, hp0, hp0_eq⟩, ⟨q1, hq1, hq1_eq⟩⟩
                                have hp0' : p0 = u ∨ p0 = v := by
                                  simpa [pairInput] using hp0_eq
                                have hq1' : q1 = u ∨ q1 = v := by
                                  simpa [pairInput] using hq1_eq
                                have hwmax_side : ∀ y ∈ PEqualNP.TopForm.side D a (1 - b_a),
                                    y ∈ wmax G D g := hSide_wmax a ha b_a hreach
                                have hno_other : ¬ ∃ g' < D.gates.length, (gateAt D g').op = GateOp.and ∧
                                    OrReaches N D (opnd D a (1 - b_a)) g' := by
                                  intro ⟨g', hg'len, hg'op, hreach'⟩
                                  rcases hAnd_split g' hg'len hg'op with htop' | hjunk'
                                  · exact hTop_not_in_cone a ha (1 - b_a) g' hreach' htop'
                                  · rw [hg_eq, Finset.mem_singleton] at hjunk'
                                    apply hg_nbel
                                    intro x' hx'
                                    apply ha'.2.2 x'
                                    rw [gateVal_eq_wireVal, wireVal_gate_and a ha'.1 ha'.2.1 x']
                                    rw [gateVal_eq_wireVal] at hx'
                                    have h1 := hWire_orReaches_val (opnd D a b_a) g x' (hjunk' ▸ hreach) hx'
                                    have h2 := hWire_orReaches_val (opnd D a (1 - b_a)) g x' (hjunk' ▸ hreach') hx'
                                    fin_cases b_a
                                    · exact ⟨h1, h2⟩
                                    · exact ⟨h2, h1⟩
                                have h1ba_val : wireVal (opnd D a (1 - b_a)) (pairInput u v) = true := by
                                  fin_cases b_a <;> [exact h_and.2; exact h_and.1]
                                obtain ⟨y, hy_side, hy_eq⟩ :=
                                  (wireVal_orIn_iff_no_and (opnd D a (1 - b_a)) (pairInput u v) hno_other).mp h1ba_val
                                have hy_wmax := hwmax_side y hy_side
                                have hy_uv : y = u ∨ y = v := by
                                  simpa [pairInput] using hy_eq
                                have huv_S : (u ∈ S0 ∧ v ∈ S1) ∨ (v ∈ S0 ∧ u ∈ S1) := by
                                  rcases hp0' with hpu | hpv <;> rcases hq1' with hqu | hqv
                                  · rw [hpu] at hp0; rw [hqu] at hq1
                                    exact absurd ((hI_iff u).mp (Finset.mem_inter.mpr ⟨hp0, hq1⟩)) hw_uv.1
                                  · rw [hpu] at hp0; rw [hqv] at hq1; exact Or.inl ⟨hp0, hq1⟩
                                  · rw [hpv] at hp0; rw [hqu] at hq1; exact Or.inr ⟨hp0, hq1⟩
                                  · rw [hpv] at hp0; rw [hqv] at hq1
                                    exact absurd ((hI_iff v).mp (Finset.mem_inter.mpr ⟨hp0, hq1⟩)) hw_uv.2
                                rcases huv_S with ⟨hu0, hv1⟩ | ⟨hv0, hu1⟩
                                · rcases hy_uv with hyu | hyv
                                  · rw [hyu] at hy_wmax
                                    exact hNoW0 u (Finset.mem_filter.mpr ⟨hy_wmax, hu0⟩)
                                      v (Finset.mem_sdiff.mpr ⟨hv1, Finset.notMem_singleton.mpr hw_uv.2⟩) hU_uv
                                  · rw [hyv] at hy_wmax
                                    exact hNoW1 v (Finset.mem_filter.mpr ⟨hy_wmax, hv1⟩)
                                      u (Finset.mem_sdiff.mpr ⟨hu0, Finset.notMem_singleton.mpr hw_uv.1⟩) (Sym2.eq_swap ▸ hU_uv)
                                · rcases hy_uv with hyu | hyv
                                  · rw [hyu] at hy_wmax
                                    exact hNoW1 u (Finset.mem_filter.mpr ⟨hy_wmax, hu1⟩)
                                      v (Finset.mem_sdiff.mpr ⟨hv0, Finset.notMem_singleton.mpr hw_uv.2⟩) (Sym2.eq_swap ▸ hU_uv)
                                  · rw [hyv] at hy_wmax
                                    exact hNoW0 v (Finset.mem_filter.mpr ⟨hy_wmax, hv0⟩)
                                      u (Finset.mem_sdiff.mpr ⟨hu1, Finset.notMem_singleton.mpr hw_uv.1⟩) (Sym2.eq_swap ▸ hU_uv)
                            · intro x' hx'
                              change circuitFun N D x' = true at hx'
                              rwa [hDeval] at hx'
                          · have hstar : s(u, v) ∈ PEqualNP.TopForm.starEdges G D := by
                              have hedges : s(u, v) ∈ G.edgeFinset := SimpleGraph.mem_edgeFinset.mpr hadj
                              by_contra hns
                              exact hU_uv (Finset.mem_sdiff.mpr ⟨hedges, hns⟩)
                            simp only [PEqualNP.TopForm.starEdges, Finset.mem_biUnion, Finset.mem_image,
                              Finset.mem_product, Prod.exists] at hstar
                            obtain ⟨a, ha, p0, q0, ⟨hp0, hq0⟩, hspq⟩ := hstar
                            have ha' := ha
                            simp only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range] at ha'
                            have ha_ne_g : a ≠ g := by
                              intro heq; subst heq; exact hg_nbel ha'.2.2
                            have hlen2a : (gateAt D a).inputs.length = 2 := by
                              apply hDAO.2.2; unfold gateAt; simp [List.getD_eq_getElem?_getD, ha'.1]
                            have hval0 : wireVal' (remap (opnd D a 0)) (pairInput u v) = true := by
                              refine hOrIn_D' (opnd D a 0) (Nat.lt_trans (hDAO.2.1 a ha'.1 (opnd D a 0) (by
                                have hb : (0 : ℕ) < (gateAt D a).inputs.length := by omega
                                unfold opnd; simp [hb, List.getElem_mem])) (by omega)) p0 hp0 (pairInput u v) ?_
                              rcases Sym2.eq_iff.mp hspq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [pairInput]
                            have hval1 : wireVal' (remap (opnd D a 1)) (pairInput u v) = true := by
                              refine hOrIn_D' (opnd D a 1) (Nat.lt_trans (hDAO.2.1 a ha'.1 (opnd D a 1) (by
                                have hb : (1 : ℕ) < (gateAt D a).inputs.length := by omega
                                unfold opnd; simp [hb, List.getElem_mem])) (by omega)) q0 hq0 (pairInput u v) ?_
                              rcases Sym2.eq_iff.mp hspq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [pairInput]
                            have hval_a : wireVal' (remap (N + a)) (pairInput u v) = true := by
                              obtain ⟨ja, hja, hja_lt, hja_if⟩ := hremapK_gate g w.1 a hg_len ha'.1 ha_ne_g
                              rw [← hD'_len] at hja_lt
                              have hget_a := hD'_get ja a hja_lt ha'.1 hja_if
                              dsimp [remap]
                              rw [hja, wireVal'_gate ja hja_lt, hget_a]
                              have ha01 : (D.gates[a]'ha'.1).inputs = [opnd D a 0, opnd D a 1] := by
                                have hlen2a' : (D.gates[a]'ha'.1).inputs.length = 2 := hDAO.2.2 _ (List.getElem_mem _)
                                rcases hlist : (D.gates[a]'ha'.1).inputs with _ | ⟨x0, _ | ⟨x1, _ | _⟩⟩
                                · rw [hlist] at hlen2a'; simp at hlen2a'
                                · rw [hlist] at hlen2a'; simp at hlen2a'
                                · unfold opnd gateAt; simp [List.getD_eq_getElem?_getD, ha'.1, hlist]
                                · rw [hlist] at hlen2a'; simp at hlen2a'
                              have hgetD_a : gateAt D a = D.gates[a]'ha'.1 := by
                                unfold gateAt; simp [List.getD_eq_getElem?_getD, ha'.1]
                              have ha_op : (D.gates[a]'ha'.1).op = GateOp.and := by rw [← hgetD_a]; exact ha'.2.1
                              rw [ha_op, ha01]
                              have hgat_a : gateAt D' ja = D'.gates[ja]'hja_lt := by
                                unfold gateAt; simp [List.getD_eq_getElem?_getD, hja_lt]
                              have hra0 : remap (opnd D a 0) < N + ja :=
                                hD'_AO2.2.1 ja hja_lt (remap (opnd D a 0)) (by rw [hgat_a, hget_a, ha01]; simp)
                              have hra1 : remap (opnd D a 1) < N + ja :=
                                hD'_AO2.2.1 ja hja_lt (remap (opnd D a 1)) (by rw [hgat_a, hget_a, ha01]; simp)
                              simp [GateOp.eval, hra0, hra1, hval0, hval1]
                            have hreach_out := hTop_orReaches_out a ha
                            have hLift : ∀ i, OrReaches N D i a →
                                wireVal' (remap i) (pairInput u v) = true := by
                              intro i hi
                              have hi' := (orReaches_reach a i hi).1
                              induction hi' using Relation.ReflTransGen.head_induction_on with
                              | refl => exact hval_a
                              | @head i_cur v_i hstep _ ih =>
                                obtain ⟨k, hk_len, rfl, hkop, hv_mem, hv_lt⟩ := hstep
                                have hk_ne_g : k ≠ g := by
                                  intro heq; subst heq; rw [hg_op] at hkop; cases hkop
                                obtain ⟨jk, hjk, hjk_lt, hjk_if⟩ := hremapK_gate g w.1 k hg_len hk_len hk_ne_g
                                rw [← hD'_len] at hjk_lt
                                have hget_k := hD'_get jk k hjk_lt hk_len hjk_if
                                dsimp [remap]
                                rw [hjk, wireVal'_gate jk hjk_lt, hget_k]
                                have hgetD_k : gateAt D k = D.gates[k]'hk_len := by
                                  unfold gateAt; simp [List.getD_eq_getElem?_getD, hk_len]
                                rw [hgetD_k] at hkop hv_mem; rw [hkop]
                                simp only [GateOp.eval, List.any_map, List.any_eq_true]
                                refine ⟨v_i, hv_mem, ?_⟩
                                have hgat_k : gateAt D' jk = D'.gates[jk]'hjk_lt := by
                                  unfold gateAt; simp [List.getD_eq_getElem?_getD, hjk_lt]
                                have hrv_lt : remap v_i < N + jk :=
                                  hD'_AO2.2.1 jk hjk_lt (remap v_i) (by rw [hgat_k, hget_k]; exact List.mem_map_of_mem hv_mem)
                                simp [hrv_lt, ih (reach_orReaches ‹_› a rfl ha'.1)]
                            exact hLift D.output hreach_out
                      have hMono_x : ∀ i, i < N + D'.gates.length →
                          wireVal' i (pairInput u v) = true → wireVal' i x = true := by
                        intro i
                        induction i using Nat.strong_induction_on with
                        | ind i ih =>
                          intro hi hval
                          by_cases hiN : i < N
                          · rw [wireVal'_lt i hiN (pairInput u v)] at hval
                            rw [wireVal'_lt i hiN x]
                            have h1 : (⟨i, hiN⟩ : Fin N) = u ∨ (⟨i, hiN⟩ : Fin N) = v := by
                              simpa [pairInput] using hval
                            rcases h1 with rfl | rfl <;> assumption
                          · obtain ⟨j, rfl⟩ : ∃ j, i = N + j := ⟨i - N, by omega⟩
                            have hj : j < D'.gates.length := by omega
                            have hlen2 : (D'.gates[j]'hj).inputs.length = 2 :=
                              hD'_AO2.2.2 _ (List.getElem_mem _)
                            obtain ⟨a0, a1, ha01⟩ : ∃ a0 a1, (D'.gates[j]'hj).inputs = [a0, a1] := by
                              rcases hlist : (D'.gates[j]'hj).inputs with _ | ⟨a0, _ | ⟨a1, _ | _⟩⟩ <;>
                                simp [hlist] at hlen2
                              exact ⟨a0, a1, rfl⟩
                            have hgat' : gateAt D' j = D'.gates[j]'hj := by
                              unfold gateAt; simp [List.getD_eq_getElem?_getD, hj]
                            have ha0_lt : a0 < N + j := hD'_AO2.2.1 j hj a0 (by rw [hgat', ha01]; simp)
                            have ha1_lt : a1 < N + j := hD'_AO2.2.1 j hj a1 (by rw [hgat', ha01]; simp)
                            rw [wireVal'_gate j hj (pairInput u v), ha01] at hval
                            rw [wireVal'_gate j hj x, ha01]
                            simp only [List.map_cons, List.map_nil, ha0_lt, ha1_lt, ↓reduceIte] at hval ⊢
                            rcases hD'_AO2.1 (D'.gates[j]'hj) (List.getElem_mem _) with hop | hop
                            · rw [hop] at hval ⊢
                              simp only [GateOp.eval, List.all_cons, List.all_nil, Bool.and_true,
                                Bool.and_eq_true] at hval ⊢
                              exact ⟨ih a0 ha0_lt (Nat.lt_trans ha0_lt hi) hval.1,
                                ih a1 ha1_lt (Nat.lt_trans ha1_lt hi) hval.2⟩
                            · rw [hop] at hval ⊢
                              simp only [GateOp.eval, List.any_cons, List.any_nil, Bool.or_false,
                                Bool.or_eq_true] at hval ⊢
                              rcases hval with h0 | h1
                              · exact Or.inl (ih a0 ha0_lt (Nat.lt_trans ha0_lt hi) h0)
                              · exact Or.inr (ih a1 ha1_lt (Nat.lt_trans ha1_lt hi) h1)
                      exact hMono_x (remap D.output) hout'_lt_remap hpair_D'
                  have hle := hDleast.2.2 D' hD'_AO2 hD'_eval
                  omega
                have hDelete_const : ∀ k0 : ℕ, k0 < D.gates.length →
                    (∀ x : Fin N → Bool, wireVal (N + k0) x = x w) → False := by
                  intro k0 hk0_len hk0_val
                  clear charge compileStars h4 hc hDtop hDsize hmin hLeast orSets_len orSets_char hGML hj2 cones_char hOneCover hNoDead hNo4 hcard hW0_adj_S1 hW1_adj_S0
                  have hout0_ne : D.output ≠ N + k0 := by
                    intro heq
                    have h1 : circuitFun N D (fun i => decide (i = w)) = true := by
                      change wireVal D.output (fun i => decide (i = w)) = true
                      rw [heq, hk0_val]; simp
                    rw [hDeval, hSingle_false w] at h1; cases h1
                  obtain ⟨D0', hD0'_eq⟩ : ∃ x, x = eraseCircuit k0 w.1 := ⟨_, rfl⟩
                  have hD0'_len : D0'.gates.length = D.gates.length - 1 := by
                    rw [hD0'_eq]; exact hErase_len k0 w.1 hk0_len
                  have hD0'_AO2 : IsAO2 N D0' := by
                    rw [hD0'_eq]; exact hErase_AO2 k0 w.1 hk0_len w.isLt
                  have hAgreeAll : ∀ i, i < N + D0'.gates.length → ∀ x,
                      wireVal_gs D0'.gates i x = wireVal (origK k0 i) x := by
                    intro i
                    induction i using Nat.strong_induction_on with
                    | ind i ih =>
                      intro hi x
                      by_cases hiN : i < N
                      · have horig : origK k0 i = i := horigK_lt k0 i (Nat.lt_of_lt_of_le hiN (Nat.le_add_right N k0))
                        rw [horig, hwire_lt D0'.gates i hiN x, wireVal_lt ⟨i, hiN⟩ x]
                      · obtain ⟨j, hj_eq⟩ : ∃ j, i = N + j := ⟨i - N, by omega⟩
                        subst hj_eq
                        have hj : j < D0'.gates.length := Nat.lt_of_add_lt_add_left hi
                        have hj' : j < D.gates.length - 1 := by rwa [hD0'_len] at hj
                        obtain ⟨k, hk_lt, hNk, hjk⟩ : ∃ k, k < D.gates.length ∧ origK k0 (N + j) = N + k ∧ k = (if j < k0 then j else j + 1) := by
                          by_cases hjk0 : j < k0
                          · exact ⟨j, by omega, horigK_lt k0 (N + j) (Nat.add_lt_add_left hjk0 N), (if_pos hjk0).symm⟩
                          · exact ⟨j + 1, by omega, by rw [horigK_ge k0 (N + j) (Nat.add_le_add_left (not_lt.mp hjk0) N), Nat.add_assoc], (if_neg hjk0).symm⟩
                        have hget : D0'.gates[j]'hj = ⟨(D.gates[k]'hk_lt).op, (D.gates[k]'hk_lt).inputs.map (remapK k0 w.1)⟩ := by
                          have hj0 : j < (eraseCircuit k0 w.1).gates.length := by rwa [← hD0'_eq]
                          simpa only [← hD0'_eq] using hErase_get k0 w.1 j k hj0 hk_lt hjk
                        have hget_D := hgateAt_D k hk_lt
                        have hw0' := hwire_gate D0'.gates j hj x
                        rw [hget] at hw0'
                        let a0 := opnd D k 0
                        let a1 := opnd D k 1
                        have ha01 : (D.gates[k]'hk_lt).inputs = [a0, a1] := by
                          rw [← hget_D]; exact hgateAt_D_inputs k hk_lt
                        have hra_lt : ∀ inp, inp ∈ [a0, a1] → remapK k0 w.1 inp < N + j := fun inp hinp =>
                          hD0'_AO2.2.1 j hj (remapK k0 w.1 inp) (by
                            have hgat : gateAt D0' j = D0'.gates[j]'hj := by
                              unfold gateAt; simp [List.getD_eq_getElem?_getD, hj]
                            rw [hgat, hget, ha01]
                            exact List.mem_map_of_mem hinp)
                        have hra0_lt := hra_lt a0 (by simp only [List.mem_cons, true_or])
                        have hra1_lt := hra_lt a1 (by simp only [List.mem_cons, List.mem_nil_iff, or_false, or_true])
                        have hval_inp : ∀ inp ∈ [a0, a1],
                            wireVal_gs D0'.gates (remapK k0 w.1 inp) x = wireVal inp x := by
                          intro inp hinp
                          have hrinp_lt := hra_lt inp hinp
                          by_cases heq : inp = N + k0
                          · subst heq
                            rw [hremapK_eq k0 w.1, hk0_val, hwire_lt D0'.gates w.1 w.isLt x]
                          · have h1 := ih (remapK k0 w.1 inp) hrinp_lt (by omega) x
                            rwa [horigK_remap k0 w.1 inp heq] at h1
                        have h0eq : opnd D k 0 = a0 := by unfold opnd; rw [hget_D, ha01]; rfl
                        have h1eq : opnd D k 1 = a1 := by unfold opnd; rw [hget_D, ha01]; rfl
                        rw [hw0', ha01, hNk, wireVal_gate k hk_lt x, h0eq, h1eq, hget_D]
                        simp only [List.map_cons, List.map_nil, hra0_lt, hra1_lt, ↓reduceIte]
                        rw [hval_inp a0 (by simp only [List.mem_cons, true_or]),
                          hval_inp a1 (by simp only [List.mem_cons, List.mem_nil_iff, or_false, or_true])]
                  have hD0'_eval : circuitFun N D0' = graphFun G ∅ := by
                    ext x
                    have hcf : circuitFun N D0' x = wireVal_gs D0'.gates (remapK k0 w.1 D.output) x := by
                      have hd0' : D0'.output = remapK k0 w.1 D.output := by rw [hD0'_eq, herase_eq]
                      rw [← hd0', hwire_gs_eq]; rfl
                    have hout0'_lt : remapK k0 w.1 D.output < N + D0'.gates.length := by
                      rw [hD0'_len]
                      by_cases hlt : D.output < N + k0
                      · rw [hremapK_lt k0 w.1 D.output hlt]; omega
                      · have hgt : N + k0 < D.output := Nat.lt_of_le_of_ne (not_lt.mp hlt) hout0_ne.symm
                        rw [hremapK_gt k0 w.1 D.output hgt]; omega
                    rw [hcf, hAgreeAll (remapK k0 w.1 D.output) hout0'_lt x, horigK_remap k0 w.1 D.output hout0_ne]
                    exact congrFun hDeval x
                  have hle := hDleast.2.2 D0' hD0'_AO2 hD0'_eval
                  have hD0'_lt : D0'.size < D.size := by
                    change D0'.gates.length < D.gates.length; rw [hD0'_len]; omega
                  omega
                have hNoFalse : ∀ k0 < D.gates.length, ∃ x : Fin N → Bool, wireVal (N + k0) x = true := by
                  clear charge compileStars h4 hc hDtop hDsize hmin hLeast orSets_len orSets_char hGML hj2 cones_char hOneCover hNoDead hNo4 hcard hW0_adj_S1 hW1_adj_S0
                  by_contra! hExF
                  let Fgates : Finset ℕ := (Finset.range D.gates.length).filter
                    (fun k => ∀ x : Fin N → Bool, wireVal (N + k) x = false)
                  have hF_ne : Fgates.Nonempty := by
                    obtain ⟨k0, hk0, hkf⟩ := hExF
                    exact ⟨k0, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk0, fun x => by
                      cases h : wireVal (N + k0) x
                      · rfl
                      · exact absurd h (hkf x)⟩⟩
                  let kmax := Fgates.max' hF_ne
                  have hkmax_mem : kmax ∈ Fgates := Finset.max'_mem Fgates hF_ne
                  have hkmax_len : kmax < D.gates.length := Finset.mem_range.mp (Finset.mem_filter.mp hkmax_mem).1
                  have hkmax_val : ∀ x, wireVal (N + kmax) x = false := (Finset.mem_filter.mp hkmax_mem).2
                  have hkmax_max : ∀ k, k ∈ Fgates → k ≤ kmax := fun k hk => Finset.le_max' Fgates k hk
                  have houtF_ne : D.output ≠ N + kmax := by
                    intro heq
                    obtain ⟨e0, he0⟩ := hEdges
                    obtain ⟨d0, hd0, rfl⟩ := Finset.mem_image.mp (edgeFinset_eq ▸ he0)
                    have hd : circuitFun N D (pairInput (L d0.1) (R d0.2)) = true := by
                      rw [hDeval]; unfold graphFun
                      simp only [Finset.notMem_empty, false_and, exists_false, decide_false,
                        Bool.false_or, decide_eq_true_eq]
                      exact ⟨L d0.1, R d0.2, (incidence d0.1 d0.2).mpr hd0, by simp [pairInput], by simp [pairInput]⟩
                    have h1 : wireVal D.output (pairInput (L d0.1) (R d0.2)) = true := hd
                    rw [heq, hkmax_val] at h1; cases h1
                  have hNotInAnd : ∀ k < D.gates.length, (gateAt D k).op = GateOp.and →
                      N + kmax ∉ (gateAt D k).inputs := by
                    intro k hk_len hkop hmem
                    have hkF : k ∈ Fgates := by
                      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk_len, fun x => ?_⟩
                      cases h : wireVal (N + k) x
                      · rfl
                      · exfalso
                        have h1 := (wireVal_gate_and k hk_len hkop x).mp h
                        have hlen2 : (gateAt D k).inputs.length = 2 := by
                          apply hDAO.2.2; unfold gateAt; simp [List.getD_eq_getElem?_getD, hk_len]
                        obtain ⟨idx, hidx, hidx_eq⟩ := List.mem_iff_getElem.mp hmem
                        have hidx2 : idx < 2 := by omega
                        have h01 : idx = 0 ∨ idx = 1 := by omega
                        rcases h01 with rfl | rfl
                        · have h0 : opnd D k 0 = N + kmax := by
                            unfold opnd; simp [List.getD_eq_getElem?_getD, hidx, hidx_eq]
                          rw [h0, hkmax_val x] at h1; cases h1.1
                        · have h1' : opnd D k 1 = N + kmax := by
                            unfold opnd; simp [List.getD_eq_getElem?_getD, hidx, hidx_eq]
                          rw [h1', hkmax_val x] at h1; cases h1.2
                    have hlt : N + kmax < N + k := hDAO.2.1 k hk_len (N + kmax) hmem
                    have hle := hkmax_max k hkF
                    omega
                  have hBothNotF : ∀ k < D.gates.length, (gateAt D k).inputs ≠ [N + kmax, N + kmax] := by
                    intro k hk_len heq
                    have hkF : k ∈ Fgates := by
                      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk_len, fun x => ?_⟩
                      rw [wireVal_gate k hk_len x]
                      have h0 : opnd D k 0 = N + kmax := by unfold opnd; rw [heq]; simp
                      have h1 : opnd D k 1 = N + kmax := by unfold opnd; rw [heq]; simp
                      rw [h0, h1, hkmax_val x]
                      rcases hDAO.1 (gateAt D k) (by
                        unfold gateAt; simp [List.getD_eq_getElem?_getD, hk_len, List.getElem_mem]) with hand | hor
                      · rw [hand]; rfl
                      · rw [hor]; rfl
                    have hlt : N + kmax < N + k := hDAO.2.1 k hk_len (N + kmax) (by rw [heq]; simp)
                    have hle := hkmax_max k hkF
                    omega
                  let remapF : ℕ → ℕ := fun i =>
                    if N + kmax < i then i - 1 else i
                  let origF : ℕ → ℕ := fun i =>
                    if i < N + kmax then i else i + 1
                  have hremapF_lt : ∀ i, i < N + kmax → remapF i = i := fun i h => by
                    dsimp [remapF]; exact if_neg (Nat.not_lt_of_ge (Nat.le_of_lt h))
                  have hremapF_gt : ∀ i, N + kmax < i → remapF i = i - 1 := fun i h => by
                    dsimp [remapF]; exact if_pos h
                  have horigF_lt : ∀ i, i < N + kmax → origF i = i := fun i h => by
                    dsimp [origF]; exact if_pos h
                  have horigF_ge : ∀ i, N + kmax ≤ i → origF i = i + 1 := fun i h => by
                    dsimp [origF]; exact if_neg (Nat.not_lt_of_ge h)
                  have horigF_remap : ∀ i, i ≠ N + kmax → origF (remapF i) = i := by
                    intro i hi
                    rcases lt_trichotomy i (N + kmax) with hlt | heq | hgt
                    · simp [remapF, origF, hlt, not_lt.mpr (le_of_lt hlt)]
                    · exact absurd heq hi
                    · simp only [remapF, hgt, ↓reduceIte, origF]; split_ifs <;> omega
                  let fixGt : Gate → Gate := fun gt =>
                    let inps' :=
                      if gt.inputs.getD 0 0 = N + kmax then
                        [remapF (gt.inputs.getD 1 0), remapF (gt.inputs.getD 1 0)]
                      else if gt.inputs.getD 1 0 = N + kmax then
                        [remapF (gt.inputs.getD 0 0), remapF (gt.inputs.getD 0 0)]
                      else gt.inputs.map remapF
                    ⟨gt.op, inps'⟩
                  obtain ⟨DF', hDF'_eq⟩ : ∃ c : Circuit, c = ⟨(D.gates.eraseIdx kmax).map fixGt, remapF D.output⟩ :=
                    ⟨_, rfl⟩
                  have hDF'_len : DF'.gates.length = D.gates.length - 1 := by
                    rw [hDF'_eq]; simp only [List.length_map, List.length_eraseIdx_of_lt hkmax_len]
                  have hDF'_get : ∀ (j k : ℕ) (hj : j < DF'.gates.length) (hk : k < D.gates.length),
                      k = (if j < kmax then j else j + 1) →
                      DF'.gates[j]'hj = fixGt (D.gates[k]'hk) := by
                    intro j k hj hk hjk
                    have hj' : j < ((D.gates.eraseIdx kmax).map fixGt).length := by
                      simpa [hDF'_eq] using hj
                    have h1 : DF'.gates[j]'hj = ((D.gates.eraseIdx kmax).map fixGt)[j]'hj' := by
                      congr 1; exact congrArg Circuit.gates hDF'_eq
                    rw [h1]; simp only [List.getElem_map, List.getElem_eraseIdx]
                    by_cases hjg : j < kmax
                    · have hkj : k = j := by rw [hjk, if_pos hjg]
                      subst hkj; simp [hjg]
                    · have hkj : k = j + 1 := by rw [hjk, if_neg hjg]
                      subst hkj; simp [hjg]
                  have horigF_gate : ∀ j, j < DF'.gates.length →
                      ∃ k, k < D.gates.length ∧ origF (N + j) = N + k ∧ k = (if j < kmax then j else j + 1) := by
                    intro j hj
                    have hj' : j < D.gates.length - 1 := by rwa [hDF'_len] at hj
                    by_cases hjk : j < kmax
                    · refine ⟨j, by omega, ?_, (if_pos hjk).symm⟩
                      exact horigF_lt (N + j) (Nat.add_lt_add_left hjk N)
                    · refine ⟨j + 1, by omega, ?_, (if_neg hjk).symm⟩
                      rw [horigF_ge (N + j) (Nat.add_le_add_left (not_lt.mp hjk) N), Nat.add_assoc]
                  have hremapF_lt_gate : ∀ j k inp, k = (if j < kmax then j else j + 1) →
                      inp < N + k → inp ≠ N + kmax → remapF inp < N + j := by
                    intro j k inp hjk hinp hne
                    by_cases hlt : inp < N + kmax
                    · rw [hremapF_lt inp hlt]
                      by_cases hjk' : j < kmax
                      · rw [if_pos hjk'] at hjk; omega
                      · rw [if_neg hjk'] at hjk; omega
                    · have hgt : N + kmax < inp := Nat.lt_of_le_of_ne (not_lt.mp hlt) hne.symm
                      rw [hremapF_gt inp hgt]
                      by_cases hjk' : j < kmax
                      · rw [if_pos hjk'] at hjk; omega
                      · rw [if_neg hjk'] at hjk; omega
                  have hDF'_AO2 : IsAO2 N DF' := by
                    refine ⟨?_, ?_, ?_⟩
                    · intro gt hgt
                      rw [hDF'_eq] at hgt
                      simp only [List.mem_map] at hgt
                      obtain ⟨gt0, hgt0, rfl⟩ := hgt
                      exact hDAO.1 gt0 (List.mem_of_mem_eraseIdx hgt0)
                    · intro j hj inp hinp
                      obtain ⟨k, hk_lt, _, hjk⟩ := horigF_gate j hj
                      have hget := hDF'_get j k hj hk_lt hjk
                      have hget_at : gateAt DF' j = DF'.gates[j]'hj := by
                        unfold gateAt; simp [List.getD_eq_getElem?_getD, hj]
                      rw [hget_at, hget] at hinp
                      have hgetD_k := hgateAt_D k hk_lt
                      let a0 := opnd D k 0
                      let a1 := opnd D k 1
                      have ha01 : (D.gates[k]'hk_lt).inputs = [a0, a1] := by
                        rw [← hgetD_k]; exact hgateAt_D_inputs k hk_lt
                      have ha0_lt : a0 < N + k := hopnd_D_lt k hk_lt 0
                      have ha1_lt : a1 < N + k := hopnd_D_lt k hk_lt 1
                      have hne_both : ¬ (a0 = N + kmax ∧ a1 = N + kmax) := by
                        intro ⟨h0, h1⟩
                        apply hBothNotF k hk_lt
                        rw [hgetD_k, ha01, h0, h1]
                      dsimp [fixGt] at hinp; rw [ha01] at hinp
                      simp only [List.getD_cons_zero, List.getD_cons_succ] at hinp
                      split_ifs at hinp with h0 h1
                      · simp only [List.mem_cons, List.mem_nil_iff, or_false, or_self] at hinp
                        subst hinp
                        exact hremapF_lt_gate j k a1 hjk ha1_lt (fun h => hne_both ⟨h0, h⟩)
                      · simp only [List.mem_cons, List.mem_nil_iff, or_false, or_self] at hinp
                        subst hinp
                        exact hremapF_lt_gate j k a0 hjk ha0_lt h0
                      · simp only [List.mem_map] at hinp
                        obtain ⟨inp0, hinp0, rfl⟩ := hinp
                        have hinp0_lt : inp0 < N + k := by
                          rcases List.mem_cons.mp hinp0 with rfl | hmem
                          · exact ha0_lt
                          · rw [List.mem_singleton.mp hmem]; exact ha1_lt
                        have hne0 : inp0 ≠ N + kmax := by
                          rcases List.mem_cons.mp hinp0 with rfl | hmem
                          · exact h0
                          · rw [List.mem_singleton.mp hmem]; exact h1
                        exact hremapF_lt_gate j k inp0 hjk hinp0_lt hne0
                    · intro gt hgt
                      rw [hDF'_eq] at hgt
                      simp only [List.mem_map] at hgt
                      obtain ⟨gt0, hgt0, rfl⟩ := hgt
                      have hlen2 : gt0.inputs.length = 2 := hDAO.2.2 gt0 (List.mem_of_mem_eraseIdx hgt0)
                      dsimp [fixGt]; split_ifs <;> simp only [List.length_cons, List.length_nil, List.length_map, hlen2]
                  obtain ⟨wireValF', hwireF'_eq⟩ : ∃ f, f = wireVal_gs DF'.gates := ⟨_, rfl⟩
                  have wireValF'_lt : ∀ i (hi : i < N) x, wireValF' i x = x ⟨i, hi⟩ := by
                    rw [hwireF'_eq]; exact hwire_lt DF'.gates
                  have wireValF'_gate : ∀ j (hj : j < DF'.gates.length) x,
                      wireValF' (N + j) x = (DF'.gates[j]'hj).op.eval
                        ((DF'.gates[j]'hj).inputs.map fun inp => if inp < N + j then wireValF' inp x else false) := by
                    rw [hwireF'_eq]; exact hwire_gate DF'.gates
                  have hAgreeF : ∀ m, m < N + DF'.gates.length →
                      ∀ x : Fin N → Bool, wireValF' m x = wireVal (origF m) x := by
                    intro m
                    induction m using Nat.strong_induction_on with
                    | ind m ih =>
                      intro hm x
                      by_cases hmN : m < N
                      · have hm_orig : origF m = m := horigF_lt m (Nat.lt_of_lt_of_le hmN (Nat.le_add_right N kmax))
                        rw [hm_orig, wireValF'_lt m hmN x, wireVal_lt ⟨m, hmN⟩ x]
                      · obtain ⟨j, hj_eq⟩ : ∃ j, m = N + j := ⟨m - N, by omega⟩
                        subst hj_eq
                        have hj : j < DF'.gates.length := Nat.lt_of_add_lt_add_left hm
                        obtain ⟨k, hk_lt, hNk, hjk⟩ := horigF_gate j hj
                        have hget := hDF'_get j k hj hk_lt hjk
                        have hget_D := hgateAt_D k hk_lt
                        have hwF' := wireValF'_gate j hj x
                        rw [hget] at hwF'
                        let a0 := opnd D k 0
                        let a1 := opnd D k 1
                        have ha01 : (D.gates[k]'hk_lt).inputs = [a0, a1] := by
                          rw [← hget_D]; exact hgateAt_D_inputs k hk_lt
                        have ha0_lt : a0 < N + k := hopnd_D_lt k hk_lt 0
                        have ha1_lt : a1 < N + k := hopnd_D_lt k hk_lt 1
                        have hne_both : ¬ (a0 = N + kmax ∧ a1 = N + kmax) := by
                          intro ⟨h0, h1⟩
                          apply hBothNotF k hk_lt; rw [hget_D, ha01, h0, h1]
                        have hlt_map : ∀ inp, inp < N + k → inp ≠ N + kmax → remapF inp < N + j :=
                          fun inp hinp hne => hremapF_lt_gate j k inp hjk hinp hne
                        have hval_ne : ∀ inp, inp < N + k → inp ≠ N + kmax →
                            wireValF' (remapF inp) x = wireVal inp x := by
                          intro inp hinp_lt hne
                          have hlt_j := hlt_map inp hinp_lt hne
                          have hih := ih (remapF inp) hlt_j (Nat.lt_trans hlt_j hm) x
                          rwa [horigF_remap inp hne] at hih
                        have h0eq : opnd D k 0 = a0 := by unfold opnd; rw [hget_D, ha01]; rfl
                        have h1eq : opnd D k 1 = a1 := by unfold opnd; rw [hget_D, ha01]; rfl
                        rw [hwF', hNk, wireVal_gate k hk_lt x, h0eq, h1eq]
                        dsimp [fixGt]; rw [ha01]
                        simp only [List.getD_cons_zero, List.getD_cons_succ]
                        split_ifs with h0 h1
                        · have hkop : (gateAt D k).op = GateOp.or := by
                            rcases hDAO.1 (gateAt D k) (hgateAt_D_mem k hk_lt) with hand | hor
                            · exact False.elim (hNotInAnd k hk_lt hand (by rw [hget_D, ha01, h0]; exact List.mem_cons_self))
                            · exact hor
                          have ha1_ne : a1 ≠ N + kmax := fun h => hne_both ⟨h0, h⟩
                          have hra1_lt := hlt_map a1 ha1_lt ha1_ne
                          rw [← hget_D, hkop]
                          simp [GateOp.eval, hra1_lt, hval_ne a1 ha1_lt ha1_ne, h0, hkmax_val x]
                        · have hkop : (gateAt D k).op = GateOp.or := by
                            rcases hDAO.1 (gateAt D k) (hgateAt_D_mem k hk_lt) with hand | hor
                            · exact False.elim (hNotInAnd k hk_lt hand (by rw [hget_D, ha01, h1]; exact List.mem_cons_of_mem _ (List.mem_cons_self)))
                            · exact hor
                          have hra0_lt := hlt_map a0 ha0_lt h0
                          rw [← hget_D, hkop]
                          simp [GateOp.eval, hra0_lt, hval_ne a0 ha0_lt h0, h1, hkmax_val x]
                        · have hra0_lt := hlt_map a0 ha0_lt h0
                          have hra1_lt := hlt_map a1 ha1_lt h1
                          rw [hget_D]
                          simp only [List.map_cons, List.map_nil, hra0_lt, hra1_lt, ↓reduceIte,
                            hval_ne a0 ha0_lt h0, hval_ne a1 ha1_lt h1]
                  have hDF'_eval : circuitFun N DF' = graphFun G ∅ := by
                    ext x
                    have hcf : circuitFun N DF' x = wireValF' (remapF D.output) x := by
                      have hdf' : DF'.output = remapF D.output := by rw [hDF'_eq]
                      rw [hwireF'_eq, ← hdf', hwire_gs_eq]; rfl
                    have houtF'_lt : remapF D.output < N + DF'.gates.length := by
                      have hout_lt : D.output < N + D.gates.length := hout_lt_D
                      rw [hDF'_len]
                      by_cases hlt : D.output < N + kmax
                      · rw [hremapF_lt D.output hlt]; omega
                      · rw [hremapF_gt D.output (Nat.lt_of_le_of_ne (not_lt.mp hlt) houtF_ne.symm)]; omega
                    rw [hcf, hAgreeF (remapF D.output) houtF'_lt x, horigF_remap D.output houtF_ne]
                    exact congrFun hDeval x
                  have hle := hDleast.2.2 DF' hDF'_AO2 hDF'_eval
                  have hDF'_lt : DF'.size < D.size := by
                    change DF'.gates.length < D.gates.length; rw [hDF'_len]; omega
                  omega
                have hOneSide_contra : ∀ (b_u : Fin 2) (u0 : Fin N),
                    u0 ∈ wmax G D g → u0 ∈ orIn N D (opnd D g b_u) →
                    (∃ v0 ∈ orIn N D (opnd D g (1 - b_u)) \ {w}, G.Adj u0 v0) →
                    (∀ u ∈ wmax G D g, u ∈ orIn N D (opnd D g b_u) → u = u0) →
                    (∀ v ∈ wmax G D g, v ∉ orIn N D (opnd D g (1 - b_u))) →
                    False := by
                  intro b_u u0 hu0_wmax hu0_Su hex_v0 hWu_eq hWv_empty
                  clear charge compileStars h4 hc hDtop hDsize hmin hLeast orSets_len orSets_char hGML hj2 hErase_AO2 hErase_get hErase_len herase_eq eraseCircuit horigK_remap hremapK_gate horigK_ge horigK_lt hremapK_gt hremapK_lt hremapK_eq origK remapK cones_char
                  let Su := orIn N D (opnd D g b_u)
                  let Sv := orIn N D (opnd D g (1 - b_u))
                  have hw_Su : w ∈ Su := by fin_cases b_u <;> [exact hw_S0; exact hw_S1]
                  have hw_Sv : w ∈ Sv := by fin_cases b_u <;> [exact hw_S1; exact hw_S0]
                  have hu0_nSv : u0 ∉ Sv := hWv_empty u0 hu0_wmax
                  have hu0_ne_w : u0 ≠ w := fun h => hu0_nSv (h ▸ hw_Sv)
                  have hu0_adj_Sv : ∀ v ∈ Sv, G.Adj u0 v := by
                    fin_cases b_u <;> dsimp [Sv]
                    · exact hW0_adj_S1 u0 (Finset.mem_filter.mpr ⟨hu0_wmax, hu0_Su⟩)
                    · exact fun v hv => (hW1_adj_S0 u0 (Finset.mem_filter.mpr ⟨hu0_wmax, hu0_Su⟩) v hv).symm
                  obtain ⟨v0, hv0_mem, _⟩ := hex_v0
                  have hv0_Sv : v0 ∈ Sv := (Finset.mem_sdiff.mp hv0_mem).1
                  have hv0_ne_w : v0 ≠ w := by simpa using (Finset.mem_sdiff.mp hv0_mem).2
                  have hSu_ge2 : 2 ≤ Su.card :=
                    Finset.one_lt_card.mpr ⟨w, hw_Su, u0, hu0_Su, hu0_ne_w.symm⟩
                  have hSv_ge2 : 2 ≤ Sv.card :=
                    Finset.one_lt_card.mpr ⟨w, hw_Sv, v0, hv0_Sv, hv0_ne_w.symm⟩
                  have hGetOpndGate : ∀ b : Fin 2, 2 ≤ (orIn N D (opnd D g b)).card →
                      ∃ hk : ℕ, hk < g ∧ opnd D g b = N + hk ∧ (gateAt D hk).op = GateOp.or := by
                    intro b hcard
                    have hlen2 : (gateAt D g).inputs.length = 2 := by
                      apply hDAO.2.2; unfold gateAt; simp [List.getD_eq_getElem?_getD, hg_len]
                    have hopnd_lt : opnd D g b < N + g := hDAO.2.1 g hg_len _ (by
                      unfold opnd; have hb : (b : ℕ) < (gateAt D g).inputs.length := by omega
                      simp [hb, List.getElem_mem])
                    have hopnd_ge : N ≤ opnd D g b := by
                      by_contra! hltN
                      have := hOrIn_lt (opnd D g b) hltN
                      omega
                    refine ⟨opnd D g b - N, by omega, by omega, ?_⟩
                    have hlt_k : opnd D g b - N < D.gates.length := by omega
                    rcases hDAO.1 (gateAt D (opnd D g b - N)) (by
                      unfold gateAt; simp [List.getD_eq_getElem?_getD, hlt_k, List.getElem_mem]) with hand | hor
                    · exfalso
                      apply hNoAnd_g b
                      refine ⟨opnd D g b - N, hlt_k, hand, ?_⟩
                      have heq : opnd D g b = N + (opnd D g b - N) := by omega
                      conv_lhs => rw [heq]
                      exact hOrReaches_self _ hlt_k
                    · exact hor
                  obtain ⟨hu, hhu_lt, hhu_eq, hhu_op⟩ := hGetOpndGate b_u hSu_ge2
                  obtain ⟨hv, hhv_lt, hhv_eq, hhv_op⟩ := hGetOpndGate (1 - b_u) hSv_ge2
                  have hhu_ne_hv : hu ≠ hv := by
                    intro heq
                    have hS_eq : Su = Sv := by dsimp [Su, Sv]; rw [hhu_eq, hhv_eq, heq]
                    exact hu0_nSv (hS_eq ▸ hu0_Su)
                  let topsUses : ℕ → Prop := fun k =>
                    ∃ a ∈ tops G D, ∃ b_a : Fin 2, OrReaches N D (opnd D a b_a) k
                  have hTop_other_side : ∀ a ∈ tops G D, ∀ b_a : Fin 2, ∀ k,
                      OrReaches N D (opnd D a b_a) k → w ∈ orIn N D (N + k) →
                      (PEqualNP.TopForm.side (n := N) D a (1 - b_a)).Nonempty ∧
                      ∀ y ∈ PEqualNP.TopForm.side D a (1 - b_a), ∀ z ∈ orIn N D (N + k), G.Adj y z := by
                    intro a ha b_a k hreach hw_k
                    have ha' := ha
                    simp only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range] at ha'
                    have hno_and : ¬ ∃ g' < D.gates.length, (gateAt D g').op = GateOp.and ∧
                        OrReaches N D (opnd D a (1 - b_a)) g' := by
                      intro ⟨g', hg'len, hg'op, hreach'⟩
                      rcases hAnd_split g' hg'len hg'op with htop' | hjunk'
                      · exact hTop_not_in_cone a ha (1 - b_a) g' hreach' htop'
                      · rw [hg_eq, Finset.mem_singleton] at hjunk'
                        subst hjunk'
                        have hw_wmax : w ∈ wmax G D g' :=
                          hSide_wmax a ha (1 - b_a) hreach' w (by
                            have hb : 1 - (1 - b_a) = b_a := by fin_cases b_a <;> rfl
                            rw [hb]; exact hOrIn_mono (opnd D a b_a) k w hreach hw_k)
                        exact hwmax_nI w hw_wmax hw_mem
                    have hne_side : (orIn N D (opnd D a (1 - b_a))).Nonempty := by
                      rw [Finset.nonempty_iff_ne_empty]
                      intro hempty
                      obtain ⟨x, hx⟩ := hNoFalse a ha'.1
                      have h1 := (wireVal_gate_and a ha'.1 ha'.2.1 x).mp hx
                      have hba_val : wireVal (opnd D a (1 - b_a)) x = true := by
                        fin_cases b_a <;> [exact h1.2; exact h1.1]
                      obtain ⟨y, hy, _⟩ := (wireVal_orIn_iff_no_and (opnd D a (1 - b_a)) x hno_and).mp hba_val
                      rw [hempty] at hy; exact absurd hy (Finset.notMem_empty _)
                    refine ⟨hne_side, fun y hy z hz => ?_⟩
                    have hz_side : z ∈ PEqualNP.TopForm.side D a b_a := hOrIn_mono (opnd D a b_a) k z hreach hz
                    fin_cases b_a
                    · exact (hTop_adj a ha z hz_side y hy).1.symm
                    · exact (hTop_adj a ha y hy z hz_side).1
                  have hNotUses_hu : ¬ topsUses hu := by
                    intro ⟨a, ha, b_a, hreach⟩
                    have hw_hu : w ∈ orIn N D (N + hu) := by rw [← hhu_eq]; exact hw_Su
                    obtain ⟨⟨y, hy⟩, hadj_y⟩ := hTop_other_side a ha b_a hu hreach hw_hu
                    have hyw := hadj_y y hy w hw_hu
                    have hyu0 := hadj_y y hy u0 (by rw [← hhu_eq]; exact hu0_Su)
                    have hu0w := hu0_adj_Sv w hw_Sv
                    obtain ⟨col, hcol⟩ := hBip
                    have h1 : col y ≠ col w := hcol hyw
                    have h2 : col y ≠ col u0 := hcol hyu0
                    have h3 : col u0 ≠ col w := hcol hu0w
                    omega
                  let C_v : Finset ℕ := (Finset.range (hv + 1)).filter
                    (fun k => OrReaches N D (N + hv) k ∧ w ∈ orIn N D (N + k))
                  have hCv_ge2 : ∀ k ∈ C_v, 2 ≤ (orIn N D (N + k)).card := by
                    intro k hk
                    simp only [C_v, Finset.mem_filter, Finset.mem_range] at hk
                    by_contra! hle1
                    have hkeq : orIn N D (N + k) = {w} :=
                      Finset.eq_singleton_iff_unique_mem.mpr ⟨hk.2.2, fun z hz =>
                        Finset.card_le_one.mp (Nat.lt_succ_iff.mp hle1) z hz w hk.2.2⟩
                    have hk_noAnd : ¬ ∃ g' < D.gates.length, (gateAt D g').op = GateOp.and ∧
                        OrReaches N D (N + k) g' := by
                      intro ⟨g', hg'len, hg'op, hreach'⟩
                      apply hNoAnd_g (1 - b_u)
                      refine ⟨g', hg'len, hg'op, ?_⟩
                      rw [hhv_eq]
                      exact reach_orReaches ((orReaches_reach k (N + hv) hk.2.1).1.trans
                        (orReaches_reach g' (N + k) hreach').1) g' rfl hg'len
                    apply hDelete_const k (by omega)
                    intro x
                    have hiff := wireVal_orIn_iff_no_and (N + k) x hk_noAnd
                    rw [hkeq] at hiff
                    cases hxw : x w
                    · cases hwk : wireVal (N + k) x
                      · rfl
                      · obtain ⟨u, hu_s, hxu⟩ := hiff.mp hwk
                        rw [Finset.mem_singleton] at hu_s; subst hu_s; rw [hxw] at hxu; cases hxu
                    · exact hiff.mpr ⟨w, Finset.mem_singleton_self w, hxw⟩
                  let S_rem : Finset (Fin N) := Sv.filter (fun v => v ≠ w ∧ s(u0, v) ∈ Ustar G D)
                  by_cases hSrem_empty : S_rem = ∅
                  · apply hDelete_contra
                    · intro u hu v hv hU_uv
                      fin_cases b_u
                      · have hu_eq : u = u0 := hWu_eq u (Finset.mem_filter.mp hu).1 (Finset.mem_filter.mp hu).2
                        subst hu_eq
                        have hv' := Finset.mem_sdiff.mp hv
                        have hv_rem : v ∈ S_rem :=
                          Finset.mem_filter.mpr ⟨hv'.1, by simpa using hv'.2, hU_uv⟩
                        rw [hSrem_empty] at hv_rem; exact absurd hv_rem (Finset.notMem_empty _)
                      · exact hWv_empty u (Finset.mem_filter.mp hu).1 (Finset.mem_filter.mp hu).2
                    · intro v hv u hu hU_vu
                      fin_cases b_u
                      · exact hWv_empty v (Finset.mem_filter.mp hv).1 (Finset.mem_filter.mp hv).2
                      · have hv_eq : v = u0 := hWu_eq v (Finset.mem_filter.mp hv).1 (Finset.mem_filter.mp hv).2
                        subst hv_eq
                        have hu' := Finset.mem_sdiff.mp hu
                        have hu_rem : u ∈ S_rem :=
                          Finset.mem_filter.mpr ⟨hu'.1, by simpa using hu'.2, Sym2.eq_swap ▸ hU_vu⟩
                        rw [hSrem_empty] at hu_rem; exact absurd hu_rem (Finset.notMem_empty _)
                  · obtain ⟨v1, hv1_rem⟩ := Finset.nonempty_iff_ne_empty.mpr hSrem_empty
                    have hCv_disj_rem : ∀ k ∈ C_v, topsUses k →
                        (orIn N D (N + k) ∩ S_rem) = ∅ := by
                      intro k hk ⟨a, ha, b_a, hreach⟩
                      rw [Finset.eq_empty_iff_forall_notMem]
                      intro v hv_int
                      have hv_k := (Finset.mem_inter.mp hv_int).1
                      have hv_rem := (Finset.mem_inter.mp hv_int).2
                      have hv_Sv := (Finset.mem_filter.mp hv_rem).1
                      have hv_ne_w := (Finset.mem_filter.mp hv_rem).2.1
                      have hv_U := (Finset.mem_filter.mp hv_rem).2.2
                      have hk_w : w ∈ orIn N D (N + k) := (Finset.mem_filter.mp hk).2.2
                      obtain ⟨⟨y, hy⟩, hadj_y⟩ := hTop_other_side a ha b_a k hreach hk_w
                      have hyw := hadj_y y hy w hk_w
                      have hyv := hadj_y y hy v hv_k
                      have hu0w := hu0_adj_Sv w hw_Sv
                      have hu0v := hu0_adj_Sv v hv_Sv
                      have hy_eq_u0 : y = u0 := by
                        by_contra hy_ne
                        have hy_nSv : y ∉ Sv := by
                          intro hySv
                          obtain ⟨col, hcol⟩ := hBip
                          have h1 : col y ≠ col w := hcol hyw
                          have h2 : col u0 ≠ col w := hcol hu0w
                          have h3 : col u0 ≠ col y := hcol (hu0_adj_Sv y hySv)
                          omega
                        have hcard2 : 1 < (Finset.univ.filter (fun z => G.Adj u0 z ∧ G.Adj y z)).card :=
                          Finset.one_lt_card.mpr ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu0w, hyw⟩,
                            v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu0v, hyv⟩, hv_ne_w.symm⟩
                        exact absurd (hNo4 u0 y (Ne.symm hy_ne)) (not_le.mpr hcard2)
                      subst hy_eq_u0
                      have hv_side : v ∈ PEqualNP.TopForm.side D a b_a :=
                        hOrIn_mono (opnd D a b_a) k v hreach hv_k
                      have hstar : s(y, v) ∈ PEqualNP.TopForm.starEdges G D := by
                        simp only [PEqualNP.TopForm.starEdges, Finset.mem_biUnion, Finset.mem_image,
                          Finset.mem_product, Prod.exists]
                        refine ⟨a, ha, ?_⟩
                        fin_cases b_a
                        · exact ⟨v, y, ⟨hv_side, hy⟩, Sym2.eq_swap⟩
                        · exact ⟨y, v, ⟨hy, hv_side⟩, rfl⟩
                      exact (Finset.mem_sdiff.mp hv_U).2 hstar
                    let K_del : Finset ℕ := C_v.filter (fun k => ¬ topsUses k)
                    have hhv_Cv : hv ∈ C_v := by
                      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_self _),
                        hOrReaches_self hv (by omega), ?_⟩
                      rw [← hhv_eq]; exact hw_Sv
                    have hhv_Kdel : hv ∈ K_del := by
                      refine Finset.mem_filter.mpr ⟨hhv_Cv, fun htu => ?_⟩
                      have hdisj := hCv_disj_rem hv hhv_Cv htu
                      have hv1_k : v1 ∈ orIn N D (N + hv) := by
                        rw [← hhv_eq]; exact (Finset.mem_filter.mp hv1_rem).1
                      have hv1_int : v1 ∈ orIn N D (N + hv) ∩ S_rem :=
                        Finset.mem_inter.mpr ⟨hv1_k, hv1_rem⟩
                      rw [hdisj] at hv1_int; exact absurd hv1_int (Finset.notMem_empty _)
                    have hKdel_lt_g : ∀ k ∈ K_del, k < g := fun k hk => by
                      have := Finset.mem_range.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hk).1).1
                      omega
                    have hKdel_ne_hu : hu ∉ K_del := by
                      intro hmem
                      have hCv := (Finset.mem_filter.mp hmem).1
                      have hreach := (Finset.mem_filter.mp hCv).2.1
                      have hsub : Su ⊆ Sv := by
                        intro x hx; dsimp [Su, Sv] at hx ⊢; rw [hhu_eq] at hx; rw [hhv_eq]
                        exact hOrIn_mono (N + hv) hu x hreach hx
                      exact hu0_nSv (hsub hu0_Su)
                    have hKdel_sub_D : ∀ k ∈ K_del, k < D.gates.length := fun k hk =>
                      Nat.lt_trans (hKdel_lt_g k hk) hg_len
                    let K_del_list : List ℕ := (List.range (hv + 1)).filter (fun k => k ∈ K_del)
                    have hKdel_list_nodup : K_del_list.Nodup :=
                      List.Nodup.filter _ List.nodup_range
                    have hKdel_list_mem : ∀ k, k ∈ K_del_list ↔ k ∈ K_del := by
                      intro k; simp only [K_del_list, List.mem_filter, List.mem_range, decide_eq_true_eq]
                      exact ⟨fun h => h.2, fun h => ⟨Finset.mem_range.mp (Finset.mem_filter.mp (Finset.mem_filter.mp h).1).1, h⟩⟩
                    have hKdel_list_len : K_del_list.length = K_del.card := by
                      rw [← List.toFinset_card_of_nodup hKdel_list_nodup]
                      congr 1; ext k; simp [hKdel_list_mem]
                    obtain ⟨kept, hkept_eq⟩ :
                        ∃ l : List ℕ, l = (List.range D.gates.length).filter (fun j => j ≠ g ∧ j ≠ hu ∧ j ∉ K_del) :=
                      ⟨_, rfl⟩
                    have hkept_nodup : kept.Nodup := by rw [hkept_eq]; exact List.Nodup.filter _ List.nodup_range
                    have hkept_mem : ∀ j, j ∈ kept ↔ j < D.gates.length ∧ j ≠ g ∧ j ≠ hu ∧ j ∉ K_del := by
                      intro j; rw [hkept_eq]; simp
                    have hkept_len : kept.length + (2 + K_del.card) = D.gates.length := by
                      have hS_sub : ({g, hu} ∪ K_del : Finset ℕ) ⊆ Finset.range D.gates.length := by
                        intro k hk
                        simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hk
                        rcases hk with (rfl | rfl) | hk
                        · exact Finset.mem_range.mpr hg_len
                        · exact Finset.mem_range.mpr (Nat.lt_trans hhu_lt hg_len)
                        · exact Finset.mem_range.mpr (hKdel_sub_D k hk)
                      have hS_card : ({g, hu} ∪ K_del : Finset ℕ).card = 2 + K_del.card := by
                        rw [Finset.card_union_of_disjoint]
                        · rw [Finset.card_pair (Nat.ne_of_gt hhu_lt)]
                        · rw [Finset.disjoint_left]
                          intro k hk hkd
                          simp only [Finset.mem_insert, Finset.mem_singleton] at hk
                          rcases hk with hkg | hkh
                          · rw [hkg] at hkd; exact Nat.lt_irrefl g (hKdel_lt_g g hkd)
                          · rw [hkh] at hkd; exact hKdel_ne_hu hkd
                      have hdiff : (Finset.range D.gates.length \ ({g, hu} ∪ K_del)).card =
                          D.gates.length - (2 + K_del.card) := by
                        rw [Finset.card_sdiff_of_subset hS_sub, Finset.card_range, hS_card]
                      have hkept_card : kept.length = (Finset.range D.gates.length \ ({g, hu} ∪ K_del)).card := by
                        rw [← List.toFinset_card_of_nodup hkept_nodup]
                        congr 1; ext j
                        simp only [List.mem_toFinset, hkept_mem, Finset.mem_sdiff, Finset.mem_range,
                          Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, not_or]
                        exact ⟨fun ⟨h1, h2, h3, h4⟩ => ⟨h1, ⟨h2, h3⟩, h4⟩,
                          fun ⟨h1, ⟨h2, h3⟩, h4⟩ => ⟨h1, h2, h3, h4⟩⟩
                      have hle : 2 + K_del.card ≤ D.gates.length := by
                        rw [← hS_card]; simpa using Finset.card_le_card hS_sub
                      rw [hkept_card, hdiff]; exact Nat.sub_add_cancel hle
                    obtain ⟨remap_kept, hremap_kept_eq⟩ : ∃ f : ℕ → ℕ, f = (fun i =>
                        if i = N + g then w.1
                        else if N ≤ i ∧ (i - N) ∈ kept then N + kept.idxOf (i - N)
                        else if i < N then i
                        else 0) := ⟨_, rfl⟩
                    have hremap_kept_lt_N : ∀ i, i < N → remap_kept i = i := by
                      intro i hi; rw [hremap_kept_eq]; dsimp only
                      rw [if_neg (Nat.ne_of_lt (Nat.lt_of_lt_of_le hi (Nat.le_add_right N g))),
                        if_neg (fun h => Nat.not_lt_of_ge h.1 hi), if_pos hi]
                    have hremap_kept_g : remap_kept (N + g) = w.1 := by
                      rw [hremap_kept_eq]; exact if_pos rfl
                    have hremap_kept_mem : ∀ k, k ∈ kept → remap_kept (N + k) = N + kept.idxOf k := by
                      intro k hk; rw [hremap_kept_eq]; dsimp only
                      have hkg : k ≠ g := ((hkept_mem k).mp hk).2.1
                      rw [if_neg (fun h => hkg (Nat.add_left_cancel h)),
                        if_pos ⟨Nat.le_add_right N k, (Nat.add_sub_cancel_left N k).symm ▸ hk⟩,
                        Nat.add_sub_cancel_left]
                    have hremap_kept_lt : ∀ j ∈ kept, ∀ inp < N + j,
                        (inp ≠ N + hu ∧ ∀ k ∈ K_del, inp ≠ N + k) →
                        remap_kept inp < N + kept.idxOf j := by
                      intro j hj inp hinp ⟨hne_hu, hne_kdel⟩
                      by_cases hinpN : inp < N
                      · rw [hremap_kept_lt_N inp hinpN]
                        exact Nat.lt_of_lt_of_le hinpN (Nat.le_add_right _ _)
                      · by_cases hinp_g : inp = N + g
                        · rw [hinp_g, hremap_kept_g]
                          exact Nat.lt_of_lt_of_le w.isLt (Nat.le_add_right _ _)
                        · have hinp_sub : inp - N < D.gates.length := by
                            have := (hkept_mem j).mp hj; omega
                          have hinp_kept : inp - N ∈ kept := by
                            rw [hkept_mem]; refine ⟨hinp_sub, ?_, ?_, ?_⟩
                            · intro heq; apply hinp_g; omega
                            · intro heq; apply hne_hu; omega
                            · intro hk; exact hne_kdel _ hk (by omega)
                          have hinp_eq : inp = N + (inp - N) := (Nat.add_sub_cancel' (Nat.le_of_not_lt hinpN)).symm
                          rw [hinp_eq, hremap_kept_mem (inp - N) hinp_kept]
                          have hidx_lt : kept.idxOf (inp - N) < kept.idxOf j := by
                            have hsorted : kept.Pairwise (· < ·) := by
                              rw [hkept_eq]; exact List.Pairwise.filter _ List.pairwise_lt_range
                            have hlt_sub : inp - N < j := by omega
                            by_contra! hle
                            have hmem1 := kept.getElem_idxOf (List.idxOf_lt_length_of_mem hinp_kept)
                            have hmem2 := kept.getElem_idxOf (List.idxOf_lt_length_of_mem hj)
                            rcases Nat.eq_or_lt_of_le hle with heq | hgt
                            · have hcon : kept[kept.idxOf (inp - N)]'(List.idxOf_lt_length_of_mem hinp_kept) =
                                  kept[kept.idxOf j]'(List.idxOf_lt_length_of_mem hj) := by
                                congr 1; exact heq.symm
                              rw [hmem1, hmem2] at hcon; omega
                            · have := List.pairwise_iff_getElem.mp hsorted _ _
                                (List.idxOf_lt_length_of_mem hj) (List.idxOf_lt_length_of_mem hinp_kept) hgt
                              rw [hmem1, hmem2] at this; omega
                          omega
                    obtain ⟨gates0, hgates0_eq⟩ : ∃ g0 : List Gate, g0 = kept.map (fun k =>
                        ⟨(gateAt D k).op, (gateAt D k).inputs.map remap_kept⟩) := ⟨_, rfl⟩
                    have hgates0_len : gates0.length = kept.length := by
                      rw [hgates0_eq, List.length_map]
                    have hgates0_get : ∀ (j : ℕ) (hj : j < gates0.length),
                        gates0[j]'hj = ⟨(gateAt D (kept[j]'(by rwa [← hgates0_len]))).op,
                          (gateAt D (kept[j]'(by rwa [← hgates0_len]))).inputs.map remap_kept⟩ := by
                      intro j hj
                      simp only [hgates0_eq, List.getElem_map]
                    have hgates0_idxOf : ∀ k (hk : k ∈ kept) (hidx : kept.idxOf k < gates0.length),
                        gates0[kept.idxOf k]'hidx = ⟨(gateAt D k).op, (gateAt D k).inputs.map remap_kept⟩ := by
                      intro k hk hidx
                      rw [hgates0_get (kept.idxOf k) hidx, kept.getElem_idxOf (List.idxOf_lt_length_of_mem hk)]
                    let foldStep : (List Gate × (ℕ → ℕ)) → ℕ → (List Gate × (ℕ → ℕ)) :=
                      fun st k =>
                        let i0 := opnd D k 0
                        let i1 := opnd D k 1
                        if (orIn N D i0 ∩ S_rem) = ∅ then
                          (st.1, fun m => if m = N + k then st.2 i1 else st.2 m)
                        else if (orIn N D i1 ∩ S_rem) = ∅ then
                          (st.1, fun m => if m = N + k then st.2 i0 else st.2 m)
                        else
                          (st.1 ++ [⟨GateOp.or, [st.2 i0, st.2 i1]⟩],
                            fun m => if m = N + k then N + st.1.length else st.2 m)
                    have hOrReaches_trans : ∀ {w0 g1 g2}, g2 < D.gates.length →
                        OrReaches N D w0 g1 → OrReaches N D (N + g1) g2 → OrReaches N D w0 g2 :=
                      fun hg2 h1 h2 => reach_orReaches ((orReaches_reach _ _ h1).1.trans (orReaches_reach _ _ h2).1) _ rfl hg2
                    have hStepOrOrAnd : ∀ j < D.gates.length, ∀ w0, Relation.ReflTransGen StepOut w0 (N + j) →
                        OrReaches N D w0 j ∨
                        ∃ a < D.gates.length, (gateAt D a).op = GateOp.and ∧
                          ∃ b_a : Fin 2, OrReaches N D (opnd D a b_a) j := by
                      intro j hj w0 hr
                      induction hr using Relation.ReflTransGen.head_induction_on with
                      | refl => exact Or.inl (hOrReaches_self j hj)
                      | @head x y hxy _ ih =>
                        rcases hxy with ⟨gx, hgx_len, rfl, hy_in⟩
                        rcases hDAO.1 (gateAt D gx) (by unfold gateAt; simp [List.getD_eq_getElem?_getD, hgx_len, List.getElem_mem]) with hand | hor
                        · have hlen2 : (gateAt D gx).inputs.length = 2 := by
                            apply hDAO.2.2; unfold gateAt; simp [List.getD_eq_getElem?_getD, hgx_len]
                          obtain ⟨idx, hidx, hidx_eq⟩ := List.mem_iff_getElem.mp hy_in
                          have hidx2 : idx < 2 := by omega
                          have hy_opnd : y = opnd D gx ⟨idx, hidx2⟩ := by
                            unfold opnd; simp [List.getD_eq_getElem?_getD, hidx, hidx_eq]
                          rcases ih with hor_yj | ⟨a, ha_len, ha_op, b_a, hreach_j⟩
                          · exact Or.inr ⟨gx, hgx_len, hand, ⟨idx, hidx2⟩, hy_opnd ▸ hor_yj⟩
                          · exact Or.inr ⟨a, ha_len, ha_op, b_a, hreach_j⟩
                        · rcases ih with hor_yj | ⟨a, ha_len, ha_op, b_a, hreach_j⟩
                          · exact Or.inl (hOrReaches_step (N + gx) gx j (hOrReaches_self gx hgx_len) hor y hy_in (hDAO.2.1 gx hgx_len y hy_in) hor_yj)
                          · exact Or.inr ⟨a, ha_len, ha_op, b_a, hreach_j⟩
                    have hk_noAnd : ∀ k ∈ K_del, ¬ ∃ g' < D.gates.length, (gateAt D g').op = GateOp.and ∧
                        OrReaches N D (N + k) g' := by
                      intro k hk ⟨g', hg'len, hg'op, hreach'⟩
                      apply hNoAnd_g (1 - b_u)
                      refine ⟨g', hg'len, hg'op, ?_⟩
                      have hk_Cv := (Finset.mem_filter.mp hk).1
                      have hreach_hv := (Finset.mem_filter.mp hk_Cv).2.1
                      rw [hhv_eq]
                      exact hOrReaches_trans hg'len hreach_hv hreach'
                    have hNoOut_to_w : ∀ k0 < D.gates.length, w ∈ orIn N D (N + k0) → ¬ topsUses k0 →
                        ∀ j < D.gates.length, j ≠ g → N + k0 ∈ (gateAt D j).inputs →
                        ∃ b_g : Fin 2, OrReaches N D (opnd D g b_g) j ∧ OrReaches N D (N + j) k0 := by
                      intro k0 hk0_len hw_k0 hntu j hj_len hj_ne_g hmem_in
                      have hk0_lt_j := hDAO.2.1 j hj_len (N + k0) hmem_in
                      have hor_jk : OrReaches N D (N + j) k0 := by
                        rcases hDAO.1 (gateAt D j) (by
                          unfold gateAt; simp [List.getD_eq_getElem?_getD, hj_len, List.getElem_mem]) with hand | hor
                        · exfalso
                          rcases hAnd_split j hj_len hand with htop | hjunk
                          · have hlen2 : (gateAt D j).inputs.length = 2 := by
                              apply hDAO.2.2; unfold gateAt; simp [List.getD_eq_getElem?_getD, hj_len]
                            obtain ⟨idx, hidx, hidx_eq⟩ := List.mem_iff_getElem.mp hmem_in
                            have hidx2 : idx < 2 := by omega
                            refine hntu ⟨j, htop, ⟨idx, hidx2⟩, ?_⟩
                            have hjeq : opnd D j ⟨idx, hidx2⟩ = N + k0 := by
                              unfold opnd; dsimp only; simp [List.getD_eq_getElem?_getD, hidx, hidx_eq]
                            rw [hjeq]; exact hOrReaches_self k0 hk0_len
                          · rw [hg_eq, Finset.mem_singleton] at hjunk; exact hj_ne_g hjunk
                        · exact hOrReaches_step (N + j) j k0 (hOrReaches_self j hj_len) hor (N + k0)
                            hmem_in hk0_lt_j (hOrReaches_self k0 hk0_len)
                      have hreach_j := hNoDead j hj_len
                      rcases hStepOrOrAnd j hj_len D.output hreach_j with hor_oj | ⟨a, ha_len, ha_op, b_a, hreach_a⟩
                      · exfalso
                        have hw_out : w ∈ orIn N D D.output :=
                          hOrIn_mono D.output k0 w (hOrReaches_trans hk0_len hor_oj hor_jk) hw_k0
                        have h1 : wireVal D.output (fun i => decide (i = w)) = true :=
                          wireVal_orIn D.output w _ hw_out (by simp)
                        have h2 : circuitFun N D (fun i => decide (i = w)) = true := h1
                        rw [hDeval, hSingle_false w] at h2; cases h2
                      · rcases hAnd_split a ha_len ha_op with htop | hjunk
                        · exact absurd ⟨a, htop, b_a, hOrReaches_trans hk0_len hreach_a hor_jk⟩ hntu
                        · rw [hg_eq, Finset.mem_singleton] at hjunk; subst hjunk
                          exact ⟨b_a, hreach_a, hor_jk⟩
                    have hKept_no_del : ∀ j ∈ kept, ∀ inp ∈ (gateAt D j).inputs,
                        inp ≠ N + hu ∧ ∀ k ∈ K_del, inp ≠ N + k := by
                      intro j hj inp hinp
                      have hj_m := (hkept_mem j).mp hj
                      refine ⟨?_, ?_⟩
                      · intro heq; rw [heq] at hinp
                        have hw_hu : w ∈ orIn N D (N + hu) := by rw [← hhu_eq]; exact hw_Su
                        obtain ⟨b_g, h1, h2⟩ := hNoOut_to_w hu (Nat.lt_trans hhu_lt hg_len) hw_hu hNotUses_hu
                          j hj_m.1 hj_m.2.1 hinp
                        have hle1 : N + j ≤ opnd D g b_g := orReaches_le _ _ h1
                        have hle2 : N + hu ≤ N + j := orReaches_le _ _ h2
                        have hopnd_lt : opnd D g b_g < N + g := hDAO.2.1 g hg_len _ (by
                          have hlen2 : (gateAt D g).inputs.length = 2 := by
                            apply hDAO.2.2; unfold gateAt; simp [List.getD_eq_getElem?_getD, hg_len]
                          unfold opnd; have hb : (b_g : ℕ) < (gateAt D g).inputs.length := by omega
                          simp [hb, List.getElem_mem])
                        by_cases hbu : b_g = b_u
                        · rw [hbu, hhu_eq] at hle1; exact hj_m.2.2.1 (by omega)
                        · have hbg_eq : b_g = 1 - b_u := by
                            rcases b_u with ⟨_ | _, _⟩ <;> rcases b_g with ⟨_ | _, _⟩ <;>
                              first | exact absurd rfl hbu | rfl | omega
                          rw [hbg_eq, hhv_eq] at h1
                          have hreach_v := hOrReaches_trans (Nat.lt_trans hhu_lt hg_len) h1 h2
                          have hsub : Su ⊆ Sv := by
                            intro z hz; dsimp [Su, Sv] at hz ⊢; rw [hhu_eq] at hz; rw [hhv_eq]
                            exact hOrIn_mono (N + hv) hu z hreach_v hz
                          exact hu0_nSv (hsub hu0_Su)
                      · intro k hk heq; rw [heq] at hinp
                        have hk_Cv := (Finset.mem_filter.mp hk).1
                        have hk_w : w ∈ orIn N D (N + k) := (Finset.mem_filter.mp hk_Cv).2.2
                        have hk_ntu : ¬ topsUses k := (Finset.mem_filter.mp hk).2
                        obtain ⟨b_g, h1, h2⟩ := hNoOut_to_w k (hKdel_sub_D k hk) hk_w hk_ntu
                          j hj_m.1 hj_m.2.1 hinp
                        by_cases hbu : b_g = b_u
                        · rw [hbu, hhu_eq] at h1
                          have hreach_uk : OrReaches N D (N + hu) k := hOrReaches_trans (hKdel_sub_D k hk) h1 h2
                          have hsub : orIn N D (N + k) ⊆ Su ∩ Sv := by
                            intro z hz; refine Finset.mem_inter.mpr ⟨?_, ?_⟩
                            · dsimp [Su]; rw [hhu_eq]; exact hOrIn_mono (N + hu) k z hreach_uk hz
                            · dsimp [Sv]; rw [hhv_eq]
                              exact hOrIn_mono (N + hv) k z (Finset.mem_filter.mp hk_Cv).2.1 hz
                          have hle1 : (orIn N D (N + k)).card ≤ 1 := by
                            have := Finset.card_le_card hsub
                            have hSuSv_eq : Su ∩ Sv = S0 ∩ S1 := by
                              fin_cases b_u <;> [rfl; exact Finset.inter_comm _ _]
                            rw [hSuSv_eq, hw_eq, Finset.card_singleton] at this; exact this
                          have := hCv_ge2 k hk_Cv; omega
                        · have hbg_eq : b_g = 1 - b_u := by
                            rcases b_u with ⟨_ | _, _⟩ <;> rcases b_g with ⟨_ | _, _⟩ <;>
                              first | exact absurd rfl hbu | rfl | omega
                          rw [hbg_eq, hhv_eq] at h1
                          have hj_lt_g : j < g := by
                            have := orReaches_le (N + hv) j h1; omega
                          have hj_Cv : j ∈ C_v := by
                            refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le (by
                              have := orReaches_le (N + hv) j h1; omega)), h1, ?_⟩
                            exact hOrIn_mono (N + j) k w h2 hk_w
                          have hj_ntu : ¬ topsUses j := fun ⟨a, ha, b_a, hreach⟩ =>
                            hk_ntu ⟨a, ha, b_a, hOrReaches_trans (hKdel_sub_D k hk) hreach h2⟩
                          exact hj_m.2.2.2 (Finset.mem_filter.mpr ⟨hj_Cv, hj_ntu⟩)
                    have hKw_ne : (K_del.filter (fun k => (orIn N D (N + k) ∩ S_rem).Nonempty)).Nonempty :=
                      ⟨hv, Finset.mem_filter.mpr ⟨hhv_Kdel, v1, Finset.mem_inter.mpr
                        ⟨by rw [← hhv_eq]; exact (Finset.mem_filter.mp hv1_rem).1, hv1_rem⟩⟩⟩
                    let K_w := K_del.filter (fun k => (orIn N D (N + k) ∩ S_rem).Nonempty)
                    let k_min := K_w.min' hKw_ne
                    have hkmin_mem : k_min ∈ K_w := Finset.min'_mem K_w hKw_ne
                    have hkmin_Kdel : k_min ∈ K_del := (Finset.mem_filter.mp hkmin_mem).1
                    have hkmin_Cv := (Finset.mem_filter.mp hkmin_Kdel).1
                    have hkmin_w : w ∈ orIn N D (N + k_min) := (Finset.mem_filter.mp hkmin_Cv).2.2
                    have hkmin_len : k_min < D.gates.length := hKdel_sub_D k_min hkmin_Kdel
                    have hkmin_op : (gateAt D k_min).op = GateOp.or := by
                      rcases hDAO.1 (gateAt D k_min) (by
                        unfold gateAt; simp [List.getD_eq_getElem?_getD, hkmin_len, List.getElem_mem]) with hand | hor
                      · exfalso; exact hk_noAnd k_min hkmin_Kdel ⟨k_min, hkmin_len, hand, hOrReaches_self k_min hkmin_len⟩
                      · exact hor
                    have hkmin_saved : (orIn N D (opnd D k_min 0) ∩ S_rem) = ∅ ∨
                        (orIn N D (opnd D k_min 1) ∩ S_rem) = ∅ := by
                      have hw_in : w ∈ orIn N D (opnd D k_min 0) ∨ w ∈ orIn N D (opnd D k_min 1) := by
                        have hlen2 : (gateAt D k_min).inputs.length = 2 := by
                          apply hDAO.2.2; unfold gateAt; simp [List.getD_eq_getElem?_getD, hkmin_len]
                        have h1 := wireVal_orIn (N + k_min) w (fun i => decide (i = w)) hkmin_w (by simp)
                        rw [wireVal_gate_or k_min hkmin_len hkmin_op] at h1
                        have hno0 : ¬ ∃ g' < D.gates.length, (gateAt D g').op = GateOp.and ∧
                            OrReaches N D (opnd D k_min 0) g' := fun ⟨g', hg', hop, hr⟩ =>
                          hk_noAnd k_min hkmin_Kdel ⟨g', hg', hop, hOrReaches_step (N + k_min) k_min g'
                            (hOrReaches_self k_min hkmin_len) hkmin_op _ (by
                              unfold opnd; have hb : (0 : ℕ) < (gateAt D k_min).inputs.length := by omega
                              simp [hb, List.getElem_mem])
                            (hDAO.2.1 k_min hkmin_len _ (by
                              unfold opnd; have hb : (0 : ℕ) < (gateAt D k_min).inputs.length := by omega
                              simp [hb, List.getElem_mem])) hr⟩
                        have hno1 : ¬ ∃ g' < D.gates.length, (gateAt D g').op = GateOp.and ∧
                            OrReaches N D (opnd D k_min 1) g' := fun ⟨g', hg', hop, hr⟩ =>
                          hk_noAnd k_min hkmin_Kdel ⟨g', hg', hop, hOrReaches_step (N + k_min) k_min g'
                            (hOrReaches_self k_min hkmin_len) hkmin_op _ (by
                              unfold opnd; have hb : (1 : ℕ) < (gateAt D k_min).inputs.length := by omega
                              simp [hb, List.getElem_mem])
                            (hDAO.2.1 k_min hkmin_len _ (by
                              unfold opnd; have hb : (1 : ℕ) < (gateAt D k_min).inputs.length := by omega
                              simp [hb, List.getElem_mem])) hr⟩
                        rcases h1 with h0 | h1
                        · left; obtain ⟨z, hz, hzw⟩ := (wireVal_orIn_iff_no_and _ _ hno0).mp h0
                          have hzw' : z = w := by simpa using hzw
                          rwa [← hzw']
                        · right; obtain ⟨z, hz, hzw⟩ := (wireVal_orIn_iff_no_and _ _ hno1).mp h1
                          have hzw' : z = w := by simpa using hzw
                          rwa [← hzw']
                      have hDisj_inp : ∀ b : Fin 2, w ∈ orIn N D (opnd D k_min b) →
                          (orIn N D (opnd D k_min b) ∩ S_rem) = ∅ := by
                        intro b hwb
                        have hlen2 : (gateAt D k_min).inputs.length = 2 := by
                          apply hDAO.2.2; unfold gateAt; simp [List.getD_eq_getElem?_getD, hkmin_len]
                        have hmem_b : opnd D k_min b ∈ (gateAt D k_min).inputs := by
                          unfold opnd; have hb : (b : ℕ) < (gateAt D k_min).inputs.length := by omega
                          simp [hb, List.getElem_mem]
                        have hlt_b := hDAO.2.1 k_min hkmin_len _ hmem_b
                        by_cases hltN : opnd D k_min b < N
                        · rw [Finset.eq_empty_iff_forall_notMem]
                          intro z hz
                          have hz1 : z = w :=
                            Finset.card_le_one.mp (hOrIn_lt _ hltN) z (Finset.mem_inter.mp hz).1 w hwb
                          exact (Finset.mem_filter.mp (Finset.mem_inter.mp hz).2).2.1 hz1
                        · obtain ⟨k0, hk0_eq⟩ : ∃ k0, opnd D k_min b = N + k0 := ⟨opnd D k_min b - N, by omega⟩
                          rw [hk0_eq] at hwb hlt_b ⊢
                          have hk0_Cv : k0 ∈ C_v := by
                            refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by
                              have := Finset.mem_range.mp (Finset.mem_filter.mp hkmin_Cv).1; omega), ?_, hwb⟩
                            exact hOrReaches_trans (by omega) (Finset.mem_filter.mp hkmin_Cv).2.1
                              (hOrReaches_step (N + k_min) k_min k0 (hOrReaches_self k_min hkmin_len)
                                hkmin_op (N + k0) (hk0_eq ▸ hmem_b) hlt_b (hOrReaches_self k0 (by omega)))
                          by_cases htu : topsUses k0
                          · exact hCv_disj_rem k0 hk0_Cv htu
                          · have hk0_Kdel : k0 ∈ K_del := Finset.mem_filter.mpr ⟨hk0_Cv, htu⟩
                            by_contra hne
                            have hne' : (orIn N D (N + k0) ∩ S_rem).Nonempty :=
                              Finset.nonempty_iff_ne_empty.mpr hne
                            have hk0_Kw : k0 ∈ K_w := Finset.mem_filter.mpr ⟨hk0_Kdel, hne'⟩
                            have hle := Finset.min'_le K_w k0 hk0_Kw
                            omega
                      rcases hw_in with h0 | h1
                      · exact Or.inl (hDisj_inp 0 h0)
                      · exact Or.inr (hDisj_inp 1 h1)
                    obtain ⟨wireVal_st, hwire_st_eq⟩ :
                        ∃ f : List Gate → ℕ → (Fin N → Bool) → Bool,
                          f = fun gs i x => (gs.foldl stepWire (List.ofFn x)).getD i false :=
                      ⟨_, rfl⟩
                    have hfold_getD : ∀ (gs : List Gate) (l : List Bool) (i : ℕ), i < l.length →
                        (gs.foldl stepWire l).getD i false = l.getD i false := by
                      intro gs l i hi
                      induction gs generalizing l with
                      | nil => rfl
                      | cons gt rest ih =>
                        have hlen_step : (stepWire l gt).length = l.length + 1 := by
                          dsimp [stepWire]; simp
                        rw [List.foldl_cons, ih (stepWire l gt) (by omega)]
                        dsimp [stepWire]
                        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
                        simp [hi, List.getElem?_append_left]
                    have hwire_append : ∀ (gs1 gs2 : List Gate) (i : ℕ) (x : Fin N → Bool),
                        i < N + gs1.length → wireVal_st (gs1 ++ gs2) i x = wireVal_st gs1 i x := by
                      intro gs1 gs2 i x hi
                      rw [hwire_st_eq]; dsimp only
                      rw [List.foldl_append]
                      have hlen1 : (gs1.foldl stepWire (List.ofFn x)).length = N + gs1.length := by
                        rw [foldl_length, List.length_ofFn]
                      exact hfold_getD gs2 _ i (by omega)
                    have hwire_lt : ∀ (gs : List Gate) (i : ℕ) (hi : i < N) (x : Fin N → Bool),
                        wireVal_st gs i x = x ⟨i, hi⟩ := by
                      intro gs i hi x
                      rw [hwire_st_eq]; dsimp only
                      rw [foldl_getD_lt gs _ i (by rw [List.length_ofFn]; exact hi), List.getD_eq_getElem?_getD]
                      simp [hi]
                    have hwire_gate : ∀ (gs : List Gate) (j : ℕ) (hj : j < gs.length) (x : Fin N → Bool),
                        wireVal_st gs (N + j) x = (gs[j]'hj).op.eval
                          ((gs[j]'hj).inputs.map fun inp => if inp < N + j then wireVal_st gs inp x else false) := by
                      intro gs j hj x
                      rw [hwire_st_eq]
                      have h := foldl_getD_gate gs (List.ofFn x) j hj
                      simp only [List.length_ofFn] at h
                      exact h
                    have hkept_AO2 : ∀ (j : ℕ) (hj : j < gates0.length),
                        ((gates0[j]'hj).op = GateOp.and ∨ (gates0[j]'hj).op = GateOp.or) ∧
                        (gates0[j]'hj).inputs.length = 2 ∧
                        ∀ inp ∈ (gates0[j]'hj).inputs, inp < N + j := by
                      intro j hj
                      have hj' : j < kept.length := by rwa [← hgates0_len]
                      have hget := hgates0_get j hj
                      have hk_mem : kept[j]'hj' ∈ kept := List.getElem_mem _
                      have hk_len : kept[j]'hj' < D.gates.length := ((hkept_mem _).mp hk_mem).1
                      have hgt_mem : gateAt D (kept[j]'hj') ∈ D.gates := by
                        unfold gateAt; simp [List.getD_eq_getElem?_getD, hk_len]
                      have hop := hDAO.1 _ hgt_mem
                      have hlen := hDAO.2.2 _ hgt_mem
                      rw [hget]
                      refine ⟨hop, ?_, ?_⟩
                      · simp [hlen]
                      · intro inp hinp
                        simp only [List.mem_map] at hinp
                        obtain ⟨inp0, hinp0, rfl⟩ := hinp
                        have h1 := hDAO.2.1 _ hk_len inp0 hinp0
                        have h2 := hKept_no_del _ hk_mem inp0 hinp0
                        have hidx : kept.idxOf (kept[j]'hj') = j :=
                          (List.Nodup.getElem_inj_iff hkept_nodup).mp
                            (kept.getElem_idxOf (List.idxOf_lt_length_of_mem hk_mem))
                        rw [← hidx]
                        exact hremap_kept_lt _ hk_mem inp0 h1 h2
                    have hkept_le : ∀ j ∈ kept, ∀ x : Fin N → Bool,
                        wireVal_st gates0 (N + kept.idxOf j) x = true → wireVal (N + j) x = true := by
                      intro j hj x hval
                      have hsorted : kept.Pairwise (· < ·) := by
                        rw [hkept_eq]; exact List.Pairwise.filter _ List.pairwise_lt_range
                      induction j using Nat.strong_induction_on with
                      | ind j ih =>
                        have hj_m := (hkept_mem j).mp hj
                        have hidx_lt : kept.idxOf j < kept.length := List.idxOf_lt_length_of_mem hj
                        have hj_lt_gs : kept.idxOf j < gates0.length := by rwa [hgates0_len]
                        have hget := hgates0_idxOf j hj hj_lt_gs
                        rw [hwire_gate gates0 (kept.idxOf j) hj_lt_gs x, hget] at hval
                        rw [wireVal_gate j hj_m.1 x]
                        let a0 := opnd D j 0
                        let a1 := opnd D j 1
                        have ha01 : (gateAt D j).inputs = [a0, a1] := hgateAt_D_inputs j hj_m.1
                        have ha0_lt : a0 < N + j := hopnd_D_lt j hj_m.1 0
                        have ha1_lt : a1 < N + j := hopnd_D_lt j hj_m.1 1
                        have hinp_le : ∀ inp < N + j, (inp ≠ N + hu ∧ ∀ k ∈ K_del, inp ≠ N + k) →
                            wireVal_st gates0 (remap_kept inp) x = true → wireVal inp x = true := by
                          intro inp hinp ⟨hne_hu, hne_kdel⟩ hvinp
                          by_cases hinpN : inp < N
                          · rw [hremap_kept_lt_N inp hinpN, hwire_lt gates0 inp hinpN x] at hvinp
                            rwa [wireVal_lt ⟨inp, hinpN⟩ x]
                          · by_cases hinp_g : inp = N + g
                            · subst hinp_g
                              rw [hremap_kept_g, hwire_lt gates0 w.1 w.isLt x] at hvinp
                              exact (hg_iff x).mpr ⟨⟨w, hw_S0, hvinp⟩, ⟨w, hw_S1, hvinp⟩⟩
                            · obtain ⟨k, rfl⟩ : ∃ k, inp = N + k := ⟨inp - N, by omega⟩
                              have hk_kept : k ∈ kept := by
                                rw [hkept_mem]; refine ⟨by omega, fun h => hinp_g (by omega),
                                  fun h => hne_hu (by omega), fun hk' => hne_kdel k hk' rfl⟩
                              rw [hremap_kept_mem k hk_kept] at hvinp
                              exact ih k (by omega) hk_kept hvinp
                        have hra0 : remap_kept a0 < N + kept.idxOf j :=
                          hremap_kept_lt j hj a0 ha0_lt (hKept_no_del j hj a0 (by rw [ha01]; simp))
                        have hra1 : remap_kept a1 < N + kept.idxOf j :=
                          hremap_kept_lt j hj a1 ha1_lt (hKept_no_del j hj a1 (by rw [ha01]; simp))
                        have h0eq : opnd D j 0 = a0 := by unfold opnd; rw [ha01]; rfl
                        have h1eq : opnd D j 1 = a1 := by unfold opnd; rw [ha01]; rfl
                        rw [ha01] at hval
                        rw [h0eq, h1eq]
                        simp only [List.map_cons, List.map_nil, hra0, hra1, ↓reduceIte, ha0_lt, ha1_lt] at hval ⊢
                        rcases hDAO.1 (gateAt D j) (by
                          unfold gateAt; simp [List.getD_eq_getElem?_getD, hj_m.1, List.getElem_mem]) with hop | hop
                        · rw [hop] at hval ⊢
                          simp only [GateOp.eval, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at hval ⊢
                          exact ⟨hinp_le a0 ha0_lt (hKept_no_del j hj a0 (by rw [ha01]; simp)) hval.1,
                            hinp_le a1 ha1_lt (hKept_no_del j hj a1 (by rw [ha01]; simp)) hval.2⟩
                        · rw [hop] at hval ⊢
                          simp only [GateOp.eval, List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true] at hval ⊢
                          rcases hval with h0 | h1
                          · exact Or.inl (hinp_le a0 ha0_lt (hKept_no_del j hj a0 (by rw [ha01]; simp)) h0)
                          · exact Or.inr (hinp_le a1 ha1_lt (hKept_no_del j hj a1 (by rw [ha01]; simp)) h1)
                    have hkept_orIn_eq : ∀ k < g, k ∉ K_del → OrReaches N D (N + hv) k →
                        ∀ x : Fin N → Bool, wireVal_st gates0 (remap_kept (N + k)) x = wireVal (N + k) x := by
                      intro k hk_lt hk_nKdel hreach_vk x
                      induction k using Nat.strong_induction_on with
                      | ind k ih =>
                        have hk_len : k < D.gates.length := Nat.lt_trans hk_lt hg_len
                        have hk_ne_hu : k ≠ hu := by
                          intro heq; subst heq
                          have hsub : Su ⊆ Sv := by
                            intro z hz; dsimp [Su, Sv] at hz ⊢; rw [hhu_eq] at hz; rw [hhv_eq]
                            exact hOrIn_mono (N + hv) k z hreach_vk hz
                          exact hu0_nSv (hsub hu0_Su)
                        have hk_kept : k ∈ kept := by
                          rw [hkept_mem]; exact ⟨hk_len, Nat.ne_of_lt hk_lt, hk_ne_hu, hk_nKdel⟩
                        have hrem_eq : remap_kept (N + k) = N + kept.idxOf k := hremap_kept_mem k hk_kept
                        have hidx_gs : kept.idxOf k < gates0.length := by
                          rw [hgates0_len]; exact List.idxOf_lt_length_of_mem hk_kept
                        have hget := hgates0_idxOf k hk_kept hidx_gs
                        rw [hrem_eq, hwire_gate gates0 (kept.idxOf k) hidx_gs x, hget, wireVal_gate k hk_len x]
                        have hlen2 : (gateAt D k).inputs.length = 2 := by
                          apply hDAO.2.2; unfold gateAt; simp [List.getD_eq_getElem?_getD, hk_len]
                        obtain ⟨a0, a1, ha01⟩ : ∃ a0 a1, (gateAt D k).inputs = [a0, a1] := by
                          rcases hlist : (gateAt D k).inputs with _ | ⟨a0, _ | ⟨a1, _ | _⟩⟩ <;>
                            simp [hlist] at hlen2
                          exact ⟨a0, a1, rfl⟩
                        have ha0_lt : a0 < N + k := hDAO.2.1 k hk_len a0 (by rw [ha01]; simp)
                        have ha1_lt : a1 < N + k := hDAO.2.1 k hk_len a1 (by rw [ha01]; simp)
                        have hkop : (gateAt D k).op = GateOp.or := by
                          rcases hDAO.1 (gateAt D k) (by
                            unfold gateAt; simp [List.getD_eq_getElem?_getD, hk_len, List.getElem_mem]) with hand | hor
                          · exfalso; apply hNoAnd_g (1 - b_u)
                            refine ⟨k, hk_len, hand, ?_⟩
                            rw [hhv_eq]; exact hreach_vk
                          · exact hor
                        have hval_inp : ∀ inp < N + k, inp ∈ (gateAt D k).inputs →
                            wireVal_st gates0 (remap_kept inp) x = wireVal inp x := by
                          intro inp hinp_lt hinp_mem
                          by_cases hinpN : inp < N
                          · rw [hremap_kept_lt_N inp hinpN, hwire_lt gates0 inp hinpN x, wireVal_lt ⟨inp, hinpN⟩ x]
                          · obtain ⟨k', rfl⟩ : ∃ k', inp = N + k' :=
                              ⟨inp - N, (Nat.add_sub_cancel' (Nat.le_of_not_lt hinpN)).symm⟩
                            have hk'_lt_k : k' < k := Nat.lt_of_add_lt_add_left hinp_lt
                            have hk'_len : k' < D.gates.length := Nat.lt_trans hk'_lt_k hk_len
                            have hk'_reach : OrReaches N D (N + hv) k' :=
                              hOrReaches_trans hk'_len hreach_vk
                                (hOrReaches_step (N + k) k k' (hOrReaches_self k hk_len)
                                  hkop (N + k') hinp_mem hinp_lt (hOrReaches_self k' hk'_len))
                            have hk'_nKdel : k' ∉ K_del := by
                              intro hk'_Kd
                              have := hKept_no_del k hk_kept (N + k') hinp_mem
                              exact this.2 k' hk'_Kd rfl
                            exact ih k' hk'_lt_k (Nat.lt_trans hk'_lt_k hk_lt) hk'_nKdel hk'_reach
                        have hra0 : remap_kept a0 < N + kept.idxOf k :=
                          hremap_kept_lt k hk_kept a0 ha0_lt (hKept_no_del k hk_kept a0 (by rw [ha01]; simp))
                        have hra1 : remap_kept a1 < N + kept.idxOf k :=
                          hremap_kept_lt k hk_kept a1 ha1_lt (hKept_no_del k hk_kept a1 (by rw [ha01]; simp))
                        have h0eq : opnd D k 0 = a0 := by unfold opnd; rw [ha01]; rfl
                        have h1eq : opnd D k 1 = a1 := by unfold opnd; rw [ha01]; rfl
                        rw [ha01, h0eq, h1eq]
                        simp only [List.map_cons, List.map_nil, hra0, hra1, ↓reduceIte,
                          hval_inp a0 ha0_lt (by rw [ha01]; simp), hval_inp a1 ha1_lt (by rw [ha01]; simp)]
                    let FoldInv : List ℕ → (List Gate × (ℕ → ℕ)) → Prop := fun pref st =>
                      (∃ ext, st.1 = gates0 ++ ext) ∧
                      st.1.length ≤ gates0.length + pref.length ∧
                      ((∃ k ∈ pref, (orIn N D (opnd D k 0) ∩ S_rem) = ∅ ∨
                          (orIn N D (opnd D k 1) ∩ S_rem) = ∅) →
                        st.1.length < gates0.length + pref.length) ∧
                      (∀ (j : ℕ) (hj : j < st.1.length), ((st.1[j]'hj).op = GateOp.and ∨
                          (st.1[j]'hj).op = GateOp.or) ∧
                        (st.1[j]'hj).inputs.length = 2 ∧
                        ∀ inp ∈ (st.1[j]'hj).inputs, inp < N + j) ∧
                      (∀ m, (m < N → st.2 m = m) ∧
                        ((∀ k ∈ pref, m ≠ N + k) → st.2 m = remap_kept m)) ∧
                      (∀ k ∈ pref, st.2 (N + k) < N + st.1.length) ∧
                      (∀ k ∈ pref, ∀ x : Fin N → Bool,
                        wireVal_st st.1 (st.2 (N + k)) x = true → ∃ v ∈ orIn N D (N + k), x v = true) ∧
                      (∀ k ∈ pref, ∀ v ∈ orIn N D (N + k) ∩ S_rem, ∀ x : Fin N → Bool,
                        x v = true → wireVal_st st.1 (st.2 (N + k)) x = true)
                    have hFoldInv_init : FoldInv [] (gates0, remap_kept) := by
                      refine ⟨⟨[], by simp⟩, le_rfl, ?_, hkept_AO2, ?_, ?_, ?_, ?_⟩
                      · intro ⟨k, hk, _⟩; simp at hk
                      · intro m; exact ⟨hremap_kept_lt_N m, fun _ => rfl⟩
                      · intro k hk; simp at hk
                      · intro k hk; simp at hk
                      · intro k hk; simp at hk
                    have hFold_res : ∀ (l : List ℕ) (pref : List ℕ) (st : List Gate × (ℕ → ℕ)),
                        l.Nodup → (∀ k ∈ l, k ∈ K_del) →
                        (∀ k ∈ l, ∀ k' ∈ pref, k' < k) →
                        l.Pairwise (· < ·) →
                        (∀ k ∈ l, ∀ k' ∈ K_del, k' < k → k' ∈ pref ∨ k' ∈ l) →
                        FoldInv pref st →
                        FoldInv (pref ++ l) (l.foldl foldStep st) := by
                      intro l
                      induction l with
                      | nil => intro pref st _ _ _ _ _ hinv; rwa [List.append_nil]
                      | cons k rest ih =>
                        intro pref st hnodup hsub_K hlt_pref hpair hcov hinv
                        rw [List.foldl_cons]
                        have hk_K : k ∈ K_del := hsub_K k List.mem_cons_self
                        have hk_lt_g : k < g := hKdel_lt_g k hk_K
                        have hk_len : k < D.gates.length := hKdel_sub_D k hk_K
                        have hk_Cv : k ∈ C_v := (Finset.mem_filter.mp hk_K).1
                        have hk_reach_hv : OrReaches N D (N + hv) k := (Finset.mem_filter.mp hk_Cv).2.1
                        have hk_op : (gateAt D k).op = GateOp.or := by
                          rcases hDAO.1 (gateAt D k) (hgateAt_D_mem k hk_len) with hand | hor
                          · exfalso; exact hk_noAnd k hk_K ⟨k, hk_len, hand, hOrReaches_self k hk_len⟩
                          · exact hor
                        have hlen2 : (gateAt D k).inputs.length = 2 := hgateAt_D_len2 k hk_len
                        have hk_not_pref : k ∉ pref := fun hm => Nat.lt_irrefl k (hlt_pref k List.mem_cons_self k hm)
                        let i0 := opnd D k 0
                        let i1 := opnd D k 1
                        have hi0_mem : i0 ∈ (gateAt D k).inputs := hopnd_D_mem k hk_len 0
                        have hi1_mem : i1 ∈ (gateAt D k).inputs := hopnd_D_mem k hk_len 1
                        have hi0_lt : i0 < N + k := hopnd_D_lt k hk_len 0
                        have hi1_lt : i1 < N + k := hopnd_D_lt k hk_len 1
                        have hst_inp_lt : ∀ inp, inp < N + k → inp ∈ (gateAt D k).inputs →
                            st.2 inp < N + st.1.length := by
                          intro inp hinp_lt hinp_mem
                          by_cases hinpN : inp < N
                          · rw [(hinv.2.2.2.2.1 inp).1 hinpN]
                            exact Nat.lt_of_lt_of_le hinpN (Nat.le_add_right _ _)
                          · obtain ⟨k', rfl⟩ : ∃ k', inp = N + k' := ⟨inp - N, by omega⟩
                            by_cases hk'_pref : k' ∈ pref
                            · exact hinv.2.2.2.2.2.1 k' hk'_pref
                            · rw [(hinv.2.2.2.2.1 (N + k')).2 (fun k'' hk'' heq => hk'_pref (Nat.add_left_cancel heq ▸ hk''))]
                              have hk'_nK : k' ∉ K_del := by
                                intro hk'K
                                rcases hcov k (by simp) k' hk'K (by omega) with hp | hl
                                · exact hk'_pref hp
                                · rcases List.mem_cons.mp hl with rfl | hrest
                                  · omega
                                  · have := List.pairwise_cons.mp hpair
                                    have := this.1 k' hrest; omega
                              have hk'_reach : OrReaches N D (N + hv) k' :=
                                hOrReaches_trans (by omega) hk_reach_hv (hOrReaches_step (N + k) k k' (hOrReaches_self k hk_len)
                                  hk_op (N + k') hinp_mem hinp_lt (hOrReaches_self k' (by omega)))
                              have hk'_ne_hu : k' ≠ hu := by
                                intro heq; subst heq
                                have hsub : Su ⊆ Sv := by
                                  intro z hz; dsimp [Su, Sv] at hz ⊢; rw [hhu_eq] at hz; rw [hhv_eq]
                                  exact hOrIn_mono (N + hv) k' z hk'_reach hz
                                exact hu0_nSv (hsub hu0_Su)
                              have hk'_kept : k' ∈ kept := by
                                rw [hkept_mem]; exact ⟨by omega, by omega, hk'_ne_hu, hk'_nK⟩
                              rw [hremap_kept_mem k' hk'_kept]
                              have := List.idxOf_lt_length_of_mem hk'_kept
                              obtain ⟨ext, hext⟩ := hinv.1
                              have hlen_st : gates0.length ≤ st.1.length := by rw [hext]; simp
                              rw [hgates0_len] at hlen_st
                              omega
                        have hst_inp_sem : ∀ inp, inp < N + k → inp ∈ (gateAt D k).inputs →
                            (∀ x : Fin N → Bool, wireVal_st st.1 (st.2 inp) x = true →
                              ∃ v ∈ orIn N D inp, x v = true) ∧
                            (∀ v ∈ orIn N D inp ∩ S_rem, ∀ x : Fin N → Bool,
                              x v = true → wireVal_st st.1 (st.2 inp) x = true) := by
                          intro inp hinp_lt hinp_mem
                          by_cases hinpN : inp < N
                          · have h_in : ⟨inp, hinpN⟩ ∈ orIn N D inp := by
                              have hno : ¬ ∃ g' < D.gates.length, (gateAt D g').op = GateOp.and ∧ OrReaches N D inp g' :=
                                fun ⟨g', _, _, hr⟩ => absurd (orReaches_le inp g' hr) (by omega)
                              obtain ⟨v, hv_in, hv_eq⟩ := (wireVal_orIn_iff_no_and inp (fun i => decide (i = ⟨inp, hinpN⟩)) hno).mp
                                (by rw [wireVal_lt ⟨inp, hinpN⟩]; simp)
                              have hv_eq' : v = ⟨inp, hinpN⟩ := by simpa using hv_eq
                              rwa [← hv_eq']
                            refine ⟨fun x hx => ?_, fun v hv x hxv => ?_⟩
                            · rw [(hinv.2.2.2.2.1 inp).1 hinpN, hwire_lt st.1 inp hinpN x] at hx
                              exact ⟨⟨inp, hinpN⟩, h_in, hx⟩
                            · have hv1 := Finset.card_le_one.mp (hOrIn_lt inp hinpN) v (Finset.mem_inter.mp hv).1 ⟨inp, hinpN⟩ h_in
                              rw [(hinv.2.2.2.2.1 inp).1 hinpN, hwire_lt st.1 inp hinpN x]
                              rwa [← hv1]
                          · obtain ⟨k', rfl⟩ : ∃ k', inp = N + k' := ⟨inp - N, by omega⟩
                            by_cases hk'_pref : k' ∈ pref
                            · exact ⟨hinv.2.2.2.2.2.2.1 k' hk'_pref, hinv.2.2.2.2.2.2.2 k' hk'_pref⟩
                            · have hrem_eq : st.2 (N + k') = remap_kept (N + k') :=
                                (hinv.2.2.2.2.1 (N + k')).2 (fun k'' hk'' heq => hk'_pref (Nat.add_left_cancel heq ▸ hk''))
                              have hk'_nK : k' ∉ K_del := by
                                intro hk'K
                                rcases hcov k (by simp) k' hk'K (by omega) with hp | hl
                                · exact hk'_pref hp
                                · rcases List.mem_cons.mp hl with rfl | hrest
                                  · omega
                                  · exact absurd ((List.pairwise_cons.mp hpair).1 k' hrest) (by omega)
                              have hk'_reach : OrReaches N D (N + hv) k' :=
                                hOrReaches_trans (by omega) hk_reach_hv (hOrReaches_step (N + k) k k' (hOrReaches_self k hk_len)
                                  hk_op (N + k') hinp_mem hinp_lt (hOrReaches_self k' (by omega)))
                              have hk'_ne_hu : k' ≠ hu := by
                                intro heq; subst heq
                                have hsub : Su ⊆ Sv := by
                                  intro z hz; dsimp [Su, Sv] at hz ⊢; rw [hhu_eq] at hz; rw [hhv_eq]
                                  exact hOrIn_mono (N + hv) k' z hk'_reach hz
                                exact hu0_nSv (hsub hu0_Su)
                              have hk'_kept : k' ∈ kept := by
                                rw [hkept_mem]; exact ⟨by omega, by omega, hk'_ne_hu, hk'_nK⟩
                              have hlt_gs0 : remap_kept (N + k') < N + gates0.length := by
                                rw [hremap_kept_mem k' hk'_kept, hgates0_len]
                                exact Nat.add_lt_add_left (List.idxOf_lt_length_of_mem hk'_kept) N
                              have hno_and_k' : ¬ ∃ g' < D.gates.length, (gateAt D g').op = GateOp.and ∧
                                  OrReaches N D (N + k') g' := fun ⟨g', hg', hop, hr⟩ =>
                                hNoAnd_g (1 - b_u) ⟨g', hg', hop, by rw [hhv_eq]; exact hOrReaches_trans hg' hk'_reach hr⟩
                              have hval_eq : ∀ x, wireVal_st st.1 (st.2 (N + k')) x = wireVal (N + k') x := by
                                intro x
                                obtain ⟨ext, hext⟩ := hinv.1
                                rw [hrem_eq, hext, hwire_append gates0 ext (remap_kept (N + k')) x hlt_gs0]
                                exact hkept_orIn_eq k' (by omega) hk'_nK hk'_reach x
                              refine ⟨fun x hx => ?_, fun v hv x hxv => ?_⟩
                              · rw [hval_eq x] at hx
                                exact (wireVal_orIn_iff_no_and (N + k') x hno_and_k').mp hx
                              · rw [hval_eq x]
                                exact wireVal_orIn (N + k') v x (Finset.mem_inter.mp hv).1 hxv
                        have hsem0 := hst_inp_sem i0 hi0_lt hi0_mem
                        have hsem1 := hst_inp_sem i1 hi1_lt hi1_mem
                        have hi0_or : ∀ v ∈ orIn N D i0, v ∈ orIn N D (N + k) := fun v hv =>
                          hOrIn_mono (N + k) k v (hOrReaches_self k hk_len) (by
                            rw [hOrIn_gate k v]
                            exact ⟨hk_len, hk_op, i0, hi0_mem, hi0_lt, hv⟩)
                        have hi1_or : ∀ v ∈ orIn N D i1, v ∈ orIn N D (N + k) := fun v hv =>
                          hOrIn_mono (N + k) k v (hOrReaches_self k hk_len) (by
                            rw [hOrIn_gate k v]
                            exact ⟨hk_len, hk_op, i1, hi1_mem, hi1_lt, hv⟩)
                        have hmem_or : ∀ v ∈ orIn N D (N + k), v ∈ orIn N D i0 ∨ v ∈ orIn N D i1 := by
                          intro v hv
                          rw [hOrIn_gate k v] at hv
                          obtain ⟨_, _, w', hw'_mem, _, hvw'⟩ := hv
                          have h1 : (gateAt D k).inputs = [i0, i1] := by
                            rcases hlist : (gateAt D k).inputs with _ | ⟨x0, _ | ⟨x1, _ | _⟩⟩ <;>
                              simp [hlist] at hlen2
                            dsimp [i0, i1, opnd]; simp [List.getD_eq_getElem?_getD, hlist]
                          rw [h1] at hw'_mem
                          rcases List.mem_cons.mp hw'_mem with rfl | h2
                          · exact Or.inl hvw'
                          · rw [List.mem_singleton.mp h2] at hvw'; exact Or.inr hvw'
                        have hstep_inv : FoldInv (pref ++ [k]) (foldStep st k) := by
                          dsimp [foldStep]
                          split_ifs with h0 h1
                          · refine ⟨hinv.1, Nat.le_trans hinv.2.1 (by rw [List.length_append, List.length_singleton]; exact Nat.le_succ _),
                              fun _ => by rw [List.length_append, List.length_singleton]; exact Nat.lt_succ_of_le hinv.2.1, hinv.2.2.2.1, ?_, ?_, ?_, ?_⟩
                            · intro m; refine ⟨fun hm => ?_, fun hne => ?_⟩
                              · dsimp only; rw [if_neg (by omega)]; exact (hinv.2.2.2.2.1 m).1 hm
                              · dsimp only; rw [if_neg (hne k (List.mem_append_right _ List.mem_cons_self))]; exact (hinv.2.2.2.2.1 m).2 (fun k' hk' => hne k' (List.mem_append_left _ hk'))
                            · intro k' hk'; simp only [List.mem_append, List.mem_singleton] at hk'
                              rcases hk' with hk' | rfl
                              · dsimp only; rw [if_neg (fun heq => hk_not_pref (by rw [← Nat.add_left_cancel heq]; exact hk'))]; exact hinv.2.2.2.2.2.1 k' hk'
                              · dsimp only; rw [if_pos rfl]; exact hst_inp_lt i1 hi1_lt hi1_mem
                            · intro k' hk' x hx; simp only [List.mem_append, List.mem_singleton] at hk'
                              rcases hk' with hk' | rfl
                              · dsimp only at hx; rw [if_neg (fun heq => hk_not_pref (by rw [← Nat.add_left_cancel heq]; exact hk'))] at hx
                                exact hinv.2.2.2.2.2.2.1 k' hk' x hx
                              · dsimp only at hx; rw [if_pos rfl] at hx
                                obtain ⟨v, hv, hxv⟩ := hsem1.1 x hx
                                exact ⟨v, hi1_or v hv, hxv⟩
                            · intro k' hk' v hv x hxv; simp only [List.mem_append, List.mem_singleton] at hk'
                              rcases hk' with hk' | rfl
                              · dsimp only; rw [if_neg (fun heq => hk_not_pref (by rw [← Nat.add_left_cancel heq]; exact hk'))]
                                exact hinv.2.2.2.2.2.2.2 k' hk' v hv x hxv
                              · dsimp only; rw [if_pos rfl]
                                have hv_k := (Finset.mem_inter.mp hv).1
                                have hv_rem := (Finset.mem_inter.mp hv).2
                                rcases hmem_or v hv_k with hv0 | hv1
                                · exfalso
                                  have hmem0 : v ∈ orIn N D i0 ∩ S_rem := Finset.mem_inter.mpr ⟨hv0, hv_rem⟩
                                  rw [h0] at hmem0; exact absurd hmem0 (Finset.notMem_empty _)
                                · exact hsem1.2 v (Finset.mem_inter.mpr ⟨hv1, hv_rem⟩) x hxv
                          · refine ⟨hinv.1, Nat.le_trans hinv.2.1 (by rw [List.length_append, List.length_singleton]; exact Nat.le_succ _),
                              fun _ => by rw [List.length_append, List.length_singleton]; exact Nat.lt_succ_of_le hinv.2.1, hinv.2.2.2.1, ?_, ?_, ?_, ?_⟩
                            · intro m; refine ⟨fun hm => ?_, fun hne => ?_⟩
                              · dsimp only; rw [if_neg (by omega)]; exact (hinv.2.2.2.2.1 m).1 hm
                              · dsimp only; rw [if_neg (hne k (List.mem_append_right _ List.mem_cons_self))]; exact (hinv.2.2.2.2.1 m).2 (fun k' hk' => hne k' (List.mem_append_left _ hk'))
                            · intro k' hk'; simp only [List.mem_append, List.mem_singleton] at hk'
                              rcases hk' with hk' | rfl
                              · dsimp only; rw [if_neg (fun heq => hk_not_pref (by rw [← Nat.add_left_cancel heq]; exact hk'))]; exact hinv.2.2.2.2.2.1 k' hk'
                              · dsimp only; rw [if_pos rfl]; exact hst_inp_lt i0 hi0_lt hi0_mem
                            · intro k' hk' x hx; simp only [List.mem_append, List.mem_singleton] at hk'
                              rcases hk' with hk' | rfl
                              · dsimp only at hx; rw [if_neg (fun heq => hk_not_pref (by rw [← Nat.add_left_cancel heq]; exact hk'))] at hx
                                exact hinv.2.2.2.2.2.2.1 k' hk' x hx
                              · dsimp only at hx; rw [if_pos rfl] at hx
                                obtain ⟨v, hv, hxv⟩ := hsem0.1 x hx
                                exact ⟨v, hi0_or v hv, hxv⟩
                            · intro k' hk' v hv x hxv; simp only [List.mem_append, List.mem_singleton] at hk'
                              rcases hk' with hk' | rfl
                              · dsimp only; rw [if_neg (fun heq => hk_not_pref (by rw [← Nat.add_left_cancel heq]; exact hk'))]
                                exact hinv.2.2.2.2.2.2.2 k' hk' v hv x hxv
                              · dsimp only; rw [if_pos rfl]
                                have hv_k := (Finset.mem_inter.mp hv).1
                                have hv_rem := (Finset.mem_inter.mp hv).2
                                rcases hmem_or v hv_k with hv0 | hv1
                                · exact hsem0.2 v (Finset.mem_inter.mpr ⟨hv0, hv_rem⟩) x hxv
                                · exfalso
                                  have hmem1 : v ∈ orIn N D i1 ∩ S_rem := Finset.mem_inter.mpr ⟨hv1, hv_rem⟩
                                  rw [h1] at hmem1; exact absurd hmem1 (Finset.notMem_empty _)
                          · have hget_last : (st.1 ++ [⟨GateOp.or, [st.2 i0, st.2 i1]⟩])[st.1.length]'(by
                                rw [List.length_append, List.length_singleton]; exact Nat.lt_succ_self _) =
                                ⟨GateOp.or, [st.2 i0, st.2 i1]⟩ := by simp
                            refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
                            · obtain ⟨ext, hext⟩ := hinv.1
                              exact ⟨ext ++ [⟨GateOp.or, [st.2 i0, st.2 i1]⟩], by rw [hext, List.append_assoc]⟩
                            · rw [List.length_append, List.length_singleton, List.length_append, List.length_singleton]
                              exact Nat.add_le_add_right hinv.2.1 1
                            · intro ⟨k', hk', hdisj⟩
                              simp only [List.mem_append, List.mem_singleton] at hk'
                              rcases hk' with hk' | rfl
                              · have hlt := hinv.2.2.1 ⟨k', hk', hdisj⟩
                                rw [List.length_append, List.length_singleton, List.length_append, List.length_singleton]
                                exact Nat.add_lt_add_right hlt 1
                              · rcases hdisj with h0' | h1'
                                · exact absurd h0' h0
                                · exact absurd h1' h1
                            · intro j hj
                              rw [List.length_append, List.length_singleton] at hj
                              by_cases hj_lt : j < st.1.length
                              · have hget : (st.1 ++ [⟨GateOp.or, [st.2 i0, st.2 i1]⟩])[j]'(by
                                    rw [List.length_append, List.length_singleton]; exact Nat.lt_succ_of_lt hj_lt) =
                                    st.1[j]'hj_lt := List.getElem_append_left hj_lt
                                rw [hget]; exact hinv.2.2.2.1 j hj_lt
                              · have hjeq : j = st.1.length := Nat.le_antisymm (Nat.lt_succ_iff.mp hj) (not_lt.mp hj_lt)
                                subst hjeq
                                rw [hget_last]
                                refine ⟨Or.inr rfl, rfl, fun inp hinp => ?_⟩
                                rcases List.mem_cons.mp hinp with rfl | h2
                                · exact hst_inp_lt i0 hi0_lt hi0_mem
                                · rw [List.mem_singleton.mp h2]; exact hst_inp_lt i1 hi1_lt hi1_mem
                            · intro m; refine ⟨fun hm => ?_, fun hne => ?_⟩
                              · dsimp only; rw [if_neg (by omega)]; exact (hinv.2.2.2.2.1 m).1 hm
                              · dsimp only; rw [if_neg (hne k (List.mem_append_right _ List.mem_cons_self))]; exact (hinv.2.2.2.2.1 m).2 (fun k' hk' => hne k' (List.mem_append_left _ hk'))
                            · intro k' hk'; simp only [List.mem_append, List.mem_singleton] at hk'
                              rcases hk' with hk' | rfl
                              · dsimp only; rw [if_neg (fun heq => hk_not_pref (by rw [← Nat.add_left_cancel heq]; exact hk'))]
                                have hlt := hinv.2.2.2.2.2.1 k' hk'
                                rw [List.length_append, List.length_singleton]; exact Nat.lt_succ_of_lt hlt
                              · dsimp only; rw [if_pos rfl, List.length_append, List.length_singleton]
                                exact Nat.add_lt_add_left (Nat.lt_succ_self _) N
                            · intro k' hk' x hx; simp only [List.mem_append, List.mem_singleton] at hk'
                              rcases hk' with hk' | rfl
                              · dsimp only at hx; rw [if_neg (fun heq => hk_not_pref (by rw [← Nat.add_left_cancel heq]; exact hk'))] at hx
                                rw [hwire_append st.1 [⟨GateOp.or, [st.2 i0, st.2 i1]⟩] _ x
                                  (hinv.2.2.2.2.2.1 k' hk')] at hx
                                exact hinv.2.2.2.2.2.2.1 k' hk' x hx
                              · dsimp only at hx; rw [if_pos rfl, hwire_gate _ st.1.length (by
                                  rw [List.length_append, List.length_singleton]; exact Nat.lt_succ_self _) x] at hx
                                rw [hget_last] at hx
                                have hlt0 := hst_inp_lt i0 hi0_lt hi0_mem
                                have hlt1 := hst_inp_lt i1 hi1_lt hi1_mem
                                simp only [GateOp.eval, List.map_cons, List.map_nil, hlt0, hlt1, ↓reduceIte,
                                  List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true] at hx
                                rcases hx with h_0 | h_1
                                · rw [hwire_append st.1 _ _ x hlt0] at h_0
                                  obtain ⟨v, hv, hxv⟩ := hsem0.1 x h_0; exact ⟨v, hi0_or v hv, hxv⟩
                                · rw [hwire_append st.1 _ _ x hlt1] at h_1
                                  obtain ⟨v, hv, hxv⟩ := hsem1.1 x h_1; exact ⟨v, hi1_or v hv, hxv⟩
                            · intro k' hk' v hv x hxv; simp only [List.mem_append, List.mem_singleton] at hk'
                              rcases hk' with hk' | rfl
                              · dsimp only; rw [if_neg (fun heq => hk_not_pref (by rw [← Nat.add_left_cancel heq]; exact hk'))]
                                rw [hwire_append st.1 _ _ x (hinv.2.2.2.2.2.1 k' hk')]
                                exact hinv.2.2.2.2.2.2.2 k' hk' v hv x hxv
                              · dsimp only; rw [if_pos rfl, hwire_gate _ st.1.length (by
                                  rw [List.length_append, List.length_singleton]; exact Nat.lt_succ_self _) x]
                                rw [hget_last]
                                have hlt0 := hst_inp_lt i0 hi0_lt hi0_mem
                                have hlt1 := hst_inp_lt i1 hi1_lt hi1_mem
                                simp only [GateOp.eval, List.map_cons, List.map_nil, hlt0, hlt1, ↓reduceIte,
                                  List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true]
                                have hv_k := (Finset.mem_inter.mp hv).1
                                have hv_rem := (Finset.mem_inter.mp hv).2
                                rcases hmem_or v hv_k with hv0 | hv1
                                · left; rw [hwire_append st.1 _ _ x hlt0]
                                  exact hsem0.2 v (Finset.mem_inter.mpr ⟨hv0, hv_rem⟩) x hxv
                                · right; rw [hwire_append st.1 _ _ x hlt1]
                                  exact hsem1.2 v (Finset.mem_inter.mpr ⟨hv1, hv_rem⟩) x hxv
                        have hih := ih (pref ++ [k]) (foldStep st k)
                          (List.nodup_cons.mp hnodup).2 (fun m hm => hsub_K m (List.mem_cons_of_mem _ hm))
                          (fun m hm m' hm' => by
                            simp only [List.mem_append, List.mem_singleton] at hm'
                            rcases hm' with hm' | rfl
                            · exact hlt_pref m (List.mem_cons_of_mem _ hm) m' hm'
                            · exact (List.pairwise_cons.mp hpair).1 m hm)
                          (List.pairwise_cons.mp hpair).2
                          (fun m hm m' hm'K hm'_lt => by
                            rcases hcov m (List.mem_cons_of_mem _ hm) m' hm'K hm'_lt with hp | hl
                            · left; exact List.mem_append_left _ hp
                            · rcases List.mem_cons.mp hl with rfl | hrest
                              · left; exact List.mem_append_right _ List.mem_cons_self
                              · right; exact hrest)
                          hstep_inv
                        rwa [List.append_assoc] at hih
                    obtain ⟨res, hres_eq⟩ : ∃ r, r = K_del_list.foldl foldStep (gates0, remap_kept) := ⟨_, rfl⟩
                    let gates_mid := res.1
                    let rep := res.2
                    let a_new : Gate := ⟨GateOp.and, [u0.1, rep (N + hv)]⟩
                    let F_new : Gate := ⟨GateOp.or, [remap_kept D.output, N + gates_mid.length]⟩
                    obtain ⟨D', hD'_eq⟩ :
                        ∃ c : Circuit, c = ⟨gates_mid ++ [a_new, F_new], N + gates_mid.length + 1⟩ :=
                      ⟨_, rfl⟩
                    have hRes_inv : FoldInv K_del_list res := by
                      rw [hres_eq]
                      have hres := hFold_res K_del_list [] (gates0, remap_kept) hKdel_list_nodup
                        (fun k hk => (hKdel_list_mem k).mp hk)
                        (fun _ _ _ hm => False.elim (List.not_mem_nil hm))
                        (List.Pairwise.filter _ List.pairwise_lt_range)
                        (fun k _ k' hk' hlt => Or.inr ((hKdel_list_mem k').mpr hk'))
                        hFoldInv_init
                      rwa [List.nil_append] at hres
                    have hD'_len_lt : D'.gates.length < D.gates.length := by
                      have h1 : gates_mid.length < gates0.length + K_del_list.length :=
                        hRes_inv.2.2.1 ⟨k_min, (hKdel_list_mem k_min).mpr hkmin_Kdel, hkmin_saved⟩
                      have hgs0 : gates0.length = kept.length := hgates0_len
                      have hD'_l : D'.gates.length = gates_mid.length + 2 := by rw [hD'_eq]; simp
                      omega
                    have hout_lt : D.output < N + D.gates.length := by
                      by_contra! hge
                      obtain ⟨e0, he0⟩ := hEdges
                      obtain ⟨d0, hd0, rfl⟩ := Finset.mem_image.mp (edgeFinset_eq ▸ he0)
                      have hd : circuitFun N D (pairInput (L d0.1) (R d0.2)) = true := by
                        rw [hDeval]; unfold graphFun
                        simp only [Finset.notMem_empty, false_and, exists_false, decide_false,
                          Bool.false_or, decide_eq_true_eq]
                        exact ⟨L d0.1, R d0.2, (incidence d0.1 d0.2).mpr hd0, by simp [pairInput], by simp [pairInput]⟩
                      have hf : circuitFun N D (pairInput (L d0.1) (R d0.2)) = false := by
                        change (D.gates.foldl stepWire (List.ofFn (pairInput (L d0.1) (R d0.2)))).getD D.output false = false
                        have hlen : (D.gates.foldl stepWire (List.ofFn (pairInput (L d0.1) (R d0.2)))).length =
                            N + D.gates.length := by rw [foldl_length, List.length_ofFn]
                        exact getD_ge _ _ (by omega)
                      rw [hd] at hf; cases hf
                    have hout_kept_lt : remap_kept D.output < N + gates_mid.length := by
                      obtain ⟨ext, hext⟩ := hRes_inv.1
                      have hgs0 : gates0.length = kept.length := hgates0_len
                      have hle : gates0.length ≤ gates_mid.length := by dsimp [gates_mid]; rw [hext]; simp
                      by_cases houtN : D.output < N
                      · rw [hremap_kept_lt_N D.output houtN]; omega
                      · by_cases hout_g : D.output = N + g
                        · rw [hout_g, hremap_kept_g]
                          exact Nat.lt_of_lt_of_le w.isLt (Nat.le_add_right _ _)
                        · obtain ⟨ko, hko⟩ : ∃ ko, D.output = N + ko := ⟨D.output - N, by omega⟩
                          have hko_ne_hu : ko ≠ hu := by
                            intro heq; subst heq
                            have h1 : wireVal D.output (fun i => decide (i = w)) = true := by
                              rw [hko]; exact wireVal_orIn (N + ko) w _ (by rw [← hhu_eq]; exact hw_Su) (by simp)
                            have h2 : circuitFun N D (fun i => decide (i = w)) = true := h1
                            rw [hDeval, hSingle_false w] at h2; cases h2
                          have hko_nKdel : ko ∉ K_del := by
                            intro hmem
                            have hk_Cv := (Finset.mem_filter.mp hmem).1
                            have hk_w := (Finset.mem_filter.mp hk_Cv).2.2
                            have h1 : wireVal D.output (fun i => decide (i = w)) = true := by
                              rw [hko]; exact wireVal_orIn (N + ko) w _ hk_w (by simp)
                            have h2 : circuitFun N D (fun i => decide (i = w)) = true := h1
                            rw [hDeval, hSingle_false w] at h2; cases h2
                          have hko_kept : ko ∈ kept := by
                            rw [hkept_mem]; exact ⟨by omega, fun h => hout_g (by omega), hko_ne_hu, hko_nKdel⟩
                          rw [hko, hremap_kept_mem ko hko_kept]; have := List.idxOf_lt_length_of_mem hko_kept; omega
                    have hD'_AO2 : IsAO2 N D' := by
                      have hD'_g : D'.gates = gates_mid ++ [a_new, F_new] := congrArg Circuit.gates hD'_eq
                      refine ⟨?_, ?_, ?_⟩
                      · intro gt hgt
                        rw [hD'_g] at hgt
                        simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hgt
                        rcases hgt with hmid | rfl | rfl
                        · obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hmid
                          exact (hRes_inv.2.2.2.1 j hj).1
                        · exact Or.inl rfl
                        · exact Or.inr rfl
                      · intro j hj inp hinp
                        have hlen_g : (gates_mid ++ [a_new, F_new]).length = gates_mid.length + 2 := by
                          rw [List.length_append, List.length_cons, List.length_cons, List.length_nil]
                        rw [hD'_g, hlen_g] at hj
                        by_cases hj_mid : j < gates_mid.length
                        · have hj_g : j < D'.gates.length := by rw [hD'_g, hlen_g]; exact Nat.lt_trans hj_mid (by omega)
                          have hget : D'.gates[j]'hj_g = gates_mid[j]'hj_mid := by
                            simp only [hD'_g]; exact List.getElem_append_left hj_mid
                          have hget_at : gateAt D' j = D'.gates[j]'hj_g := by
                            unfold gateAt; simp [List.getD_eq_getElem?_getD, hj_g]
                          rw [hget_at, hget] at hinp
                          exact (hRes_inv.2.2.2.1 j hj_mid).2.2 inp hinp
                        · have hcases : j = gates_mid.length ∨ j = gates_mid.length + 1 := by omega
                          rcases hcases with rfl | rfl
                          · have hj_g : gates_mid.length < D'.gates.length := by rw [hD'_g, hlen_g]; exact Nat.lt_succ_of_lt (Nat.lt_succ_self _)
                            have hget : D'.gates[gates_mid.length]'hj_g = a_new := by
                              simp only [hD'_g, List.getElem_append_right, le_rfl, Nat.sub_self, List.getElem_cons_zero]
                            have hget_at : gateAt D' gates_mid.length = D'.gates[gates_mid.length]'hj_g := by
                              unfold gateAt; simp only [List.getD_eq_getElem?_getD, hj_g, List.getElem?_eq_getElem, Option.getD_some]
                            rw [hget_at, hget] at hinp
                            rcases List.mem_cons.mp hinp with rfl | h2
                            · exact Nat.lt_of_lt_of_le u0.isLt (Nat.le_add_right _ _)
                            · rw [List.mem_singleton.mp h2]
                              exact hRes_inv.2.2.2.2.2.1 hv ((hKdel_list_mem hv).mpr hhv_Kdel)
                          · have hj_g : gates_mid.length + 1 < D'.gates.length := by rw [hD'_g, hlen_g]; exact Nat.lt_succ_self _
                            have hget : D'.gates[gates_mid.length + 1]'hj_g = F_new := by
                              simp only [hD'_g, List.getElem_append_right, Nat.le_succ, Nat.add_sub_cancel_left,
                                List.getElem_cons_succ, List.getElem_cons_zero]
                            have hget_at : gateAt D' (gates_mid.length + 1) = D'.gates[gates_mid.length + 1]'hj_g := by
                              unfold gateAt; simp only [List.getD_eq_getElem?_getD, hj_g, List.getElem?_eq_getElem, Option.getD_some]
                            rw [hget_at, hget] at hinp
                            rcases List.mem_cons.mp hinp with rfl | h2
                            · exact Nat.lt_trans hout_kept_lt (by omega)
                            · rw [List.mem_singleton.mp h2]; omega
                      · intro gt hgt
                        rw [hD'_g] at hgt
                        simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hgt
                        rcases hgt with hmid | rfl | rfl
                        · obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hmid
                          exact (hRes_inv.2.2.2.1 j hj).2.1
                        · rfl
                        · rfl
                    have hD'_eval : circuitFun N D' = graphFun G ∅ := by
                      ext x
                      have hcf : circuitFun N D' x = wireVal_st D'.gates D'.output x := by
                        rw [hwire_st_eq]; rfl
                      have hout_val : wireVal_st D'.gates D'.output x =
                          (wireVal_st gates_mid (remap_kept D.output) x ||
                            (x u0 && wireVal_st gates_mid (rep (N + hv)) x)) := by
                        rw [hD'_eq]
                        have hlen_g1 : (gates_mid ++ [a_new, F_new]).length = gates_mid.length + 2 := by
                          rw [List.length_append, List.length_cons, List.length_cons, List.length_nil]
                        rw [Nat.add_assoc, hwire_gate _ (gates_mid.length + 1) (by rw [hlen_g1]; exact Nat.lt_succ_self _) x]
                        have hgetF : (gates_mid ++ [a_new, F_new])[gates_mid.length + 1]'(by rw [hlen_g1]; exact Nat.lt_succ_self _) = F_new := by
                          simp only [List.getElem_append_right, Nat.le_succ, Nat.add_sub_cancel_left,
                            List.getElem_cons_succ, List.getElem_cons_zero]
                        rw [hgetF]
                        have hlt_a : N + gates_mid.length < N + (gates_mid.length + 1) := Nat.add_lt_add_left (Nat.lt_succ_self _) N
                        have hlt_o : remap_kept D.output < N + (gates_mid.length + 1) := Nat.lt_trans hout_kept_lt hlt_a
                        simp only [F_new, GateOp.eval, List.map_cons, List.map_nil, hlt_o, hlt_a, ↓reduceIte,
                          List.any_cons, List.any_nil, Bool.or_false]
                        rw [hwire_append gates_mid [a_new, F_new] _ x hout_kept_lt]
                        have ha_val : wireVal_st (gates_mid ++ [a_new, F_new]) (N + gates_mid.length) x =
                            (x u0 && wireVal_st gates_mid (rep (N + hv)) x) := by
                          rw [hwire_gate _ gates_mid.length (by rw [hlen_g1]; exact Nat.lt_succ_of_lt (Nat.lt_succ_self _)) x]
                          have hgetA : (gates_mid ++ [a_new, F_new])[gates_mid.length]'(by rw [hlen_g1]; exact Nat.lt_succ_of_lt (Nat.lt_succ_self _)) = a_new := by
                            simp only [List.getElem_append_right, le_rfl, Nat.sub_self, List.getElem_cons_zero]
                          rw [hgetA]
                          have hlt_u0 : u0.1 < N + gates_mid.length :=
                            Nat.lt_of_lt_of_le u0.isLt (Nat.le_add_right _ _)
                          have hlt_hv : rep (N + hv) < N + gates_mid.length :=
                            hRes_inv.2.2.2.2.2.1 hv ((hKdel_list_mem hv).mpr hhv_Kdel)
                          simp only [a_new, GateOp.eval, List.map_cons, List.map_nil, hlt_u0, hlt_hv, ↓reduceIte,
                            List.all_cons, List.all_nil, Bool.and_true]
                          rw [hwire_lt _ u0.1 u0.isLt x, hwire_append gates_mid [a_new, F_new] _ x hlt_hv]
                          rfl
                        rw [ha_val]; rfl
                      have hkept_out_le : wireVal_st gates_mid (remap_kept D.output) x = true →
                          graphFun G ∅ x = true := by
                        intro hval
                        obtain ⟨ext, hext⟩ := hRes_inv.1
                        have hmid_eq : gates_mid = gates0 ++ ext := hext
                        rw [hmid_eq, hwire_append gates0 ext (remap_kept D.output) x (by
                          rw [hgates0_len]
                          by_cases houtN : D.output < N
                          · rw [hremap_kept_lt_N D.output houtN]; exact Nat.lt_of_lt_of_le houtN (Nat.le_add_right _ _)
                          · by_cases hout_g : D.output = N + g
                            · rw [hout_g, hremap_kept_g]; exact Nat.lt_of_lt_of_le w.isLt (Nat.le_add_right _ _)
                            · obtain ⟨ko, hko⟩ : ∃ ko, D.output = N + ko := ⟨D.output - N, by omega⟩
                              have hko_ne_hu : ko ≠ hu := by
                                intro heq; subst heq
                                have h1 : wireVal D.output (fun i => decide (i = w)) = true := by
                                  rw [hko]; exact wireVal_orIn (N + ko) w _ (by rw [← hhu_eq]; exact hw_Su) (by simp)
                                have h2 : circuitFun N D (fun i => decide (i = w)) = true := h1
                                rw [hDeval, hSingle_false w] at h2; cases h2
                              have hko_nKdel : ko ∉ K_del := by
                                intro hmem
                                have hk_Cv := (Finset.mem_filter.mp hmem).1
                                have hk_w := (Finset.mem_filter.mp hk_Cv).2.2
                                have h1 : wireVal D.output (fun i => decide (i = w)) = true := by
                                  rw [hko]; exact wireVal_orIn (N + ko) w _ hk_w (by simp)
                                have h2 : circuitFun N D (fun i => decide (i = w)) = true := h1
                                rw [hDeval, hSingle_false w] at h2; cases h2
                              have hko_kept : ko ∈ kept := by
                                rw [hkept_mem]; exact ⟨by omega, fun h => hout_g (by omega), hko_ne_hu, hko_nKdel⟩
                              rw [hko, hremap_kept_mem ko hko_kept]
                              exact Nat.add_lt_add_left (List.idxOf_lt_length_of_mem hko_kept) N)] at hval
                        have hD_true : wireVal D.output x = true := by
                          by_cases houtN : D.output < N
                          · rw [hremap_kept_lt_N D.output houtN, hwire_lt gates0 D.output houtN x] at hval
                            rwa [wireVal_lt ⟨D.output, houtN⟩ x]
                          · by_cases hout_g : D.output = N + g
                            · rw [hout_g] at hval ⊢
                              rw [hremap_kept_g, hwire_lt gates0 w.1 w.isLt x] at hval
                              exact (hg_iff x).mpr ⟨⟨w, hw_S0, hval⟩, ⟨w, hw_S1, hval⟩⟩
                            · obtain ⟨ko, hko⟩ : ∃ ko, D.output = N + ko := ⟨D.output - N, by omega⟩
                              have hko_ne_hu : ko ≠ hu := by
                                intro heq; subst heq
                                have h1 : wireVal D.output (fun i => decide (i = w)) = true := by
                                  rw [hko]; exact wireVal_orIn (N + ko) w _ (by rw [← hhu_eq]; exact hw_Su) (by simp)
                                have h2 : circuitFun N D (fun i => decide (i = w)) = true := h1
                                rw [hDeval, hSingle_false w] at h2; cases h2
                              have hko_nKdel : ko ∉ K_del := by
                                intro hmem
                                have hk_Cv := (Finset.mem_filter.mp hmem).1
                                have hk_w := (Finset.mem_filter.mp hk_Cv).2.2
                                have h1 : wireVal D.output (fun i => decide (i = w)) = true := by
                                  rw [hko]; exact wireVal_orIn (N + ko) w _ hk_w (by simp)
                                have h2 : circuitFun N D (fun i => decide (i = w)) = true := h1
                                rw [hDeval, hSingle_false w] at h2; cases h2
                              have hko_kept : ko ∈ kept := by
                                rw [hkept_mem]; exact ⟨by omega, fun h => hout_g (by omega), hko_ne_hu, hko_nKdel⟩
                              rw [hko, hremap_kept_mem ko hko_kept] at hval; rw [hko]; exact hkept_le ko hko_kept x hval
                        change circuitFun N D x = true at hD_true
                        rwa [hDeval] at hD_true
                      cases hgf : graphFun G ∅ x
                      · rw [hcf, hout_val]
                        by_cases h1 : wireVal_st gates_mid (remap_kept D.output) x = true
                        · have := hkept_out_le h1; rw [hgf] at this; cases this
                        · have h1f : wireVal_st gates_mid (remap_kept D.output) x = false := by
                            cases h : wireVal_st gates_mid (remap_kept D.output) x <;> simp [h] at h1 ⊢
                          rw [h1f, Bool.false_or]
                          by_cases h2 : (x u0 && wireVal_st gates_mid (rep (N + hv)) x) = true
                          · simp only [Bool.and_eq_true] at h2
                            obtain ⟨v, hv_in, hxv⟩ := hRes_inv.2.2.2.2.2.2.1 hv ((hKdel_list_mem hv).mpr hhv_Kdel) x h2.2
                            have hv_Sv : v ∈ Sv := by dsimp [Sv]; rwa [hhv_eq]
                            have hadj := hu0_adj_Sv v hv_Sv
                            have hgf_true : graphFun G ∅ x = true := by
                              unfold graphFun
                              simp only [Finset.notMem_empty, false_and, exists_false, decide_false,
                                Bool.false_or, decide_eq_true_eq]
                              exact ⟨u0, v, hadj, h2.1, hxv⟩
                            rw [hgf] at hgf_true; cases hgf_true
                          · cases h : (x u0 && wireVal_st gates_mid (rep (N + hv)) x) <;> simp [h] at h2 ⊢
                      · rw [hcf, hout_val]
                        have hgf' := hgf
                        unfold graphFun at hgf'
                        simp only [Finset.notMem_empty, false_and, exists_false, decide_false,
                          Bool.false_or, decide_eq_true_eq] at hgf'
                        obtain ⟨p, q, hadj, hxp, hxq⟩ := hgf'
                        have hpq : p ≠ q := G.ne_of_adj hadj
                        by_cases hpq_rem : (p = u0 ∧ q ∈ S_rem) ∨ (q = u0 ∧ p ∈ S_rem)
                        · have h_and_t : (x u0 && wireVal_st gates_mid (rep (N + hv)) x) = true := by
                            simp only [Bool.and_eq_true]
                            rcases hpq_rem with ⟨rfl, hq⟩ | ⟨rfl, hp⟩
                            · refine ⟨hxp, hRes_inv.2.2.2.2.2.2.2 hv ((hKdel_list_mem hv).mpr hhv_Kdel) q
                                (Finset.mem_inter.mpr ⟨by rw [← hhv_eq]; exact (Finset.mem_filter.mp hq).1, hq⟩) x hxq⟩
                            · refine ⟨hxq, hRes_inv.2.2.2.2.2.2.2 hv ((hKdel_list_mem hv).mpr hhv_Kdel) p
                                (Finset.mem_inter.mpr ⟨by rw [← hhv_eq]; exact (Finset.mem_filter.mp hp).1, hp⟩) x hxp⟩
                          rw [h_and_t, Bool.or_true]
                        · have hkept_t : wireVal_st gates_mid (remap_kept D.output) x = true := by
                            obtain ⟨ext, hext⟩ := hRes_inv.1
                            have hmid_eq : gates_mid = gates0 ++ ext := hext
                            rw [hmid_eq, hwire_append gates0 ext (remap_kept D.output) x (by
                              rw [hgates0_len]
                              by_cases houtN : D.output < N
                              · rw [hremap_kept_lt_N D.output houtN]; exact Nat.lt_of_lt_of_le houtN (Nat.le_add_right _ _)
                              · by_cases hout_g : D.output = N + g
                                · rw [hout_g, hremap_kept_g]; exact Nat.lt_of_lt_of_le w.isLt (Nat.le_add_right _ _)
                                · obtain ⟨ko, hko⟩ : ∃ ko, D.output = N + ko := ⟨D.output - N, by omega⟩
                                  have hko_ne_hu : ko ≠ hu := by
                                    intro heq; subst heq
                                    have h1 : wireVal D.output (fun i => decide (i = w)) = true := by
                                      rw [hko]; exact wireVal_orIn (N + ko) w _ (by rw [← hhu_eq]; exact hw_Su) (by simp)
                                    have h2 : circuitFun N D (fun i => decide (i = w)) = true := h1
                                    rw [hDeval, hSingle_false w] at h2; cases h2
                                  have hko_nKdel : ko ∉ K_del := by
                                    intro hmem
                                    have hk_Cv := (Finset.mem_filter.mp hmem).1
                                    have hk_w := (Finset.mem_filter.mp hk_Cv).2.2
                                    have h1 : wireVal D.output (fun i => decide (i = w)) = true := by
                                      rw [hko]; exact wireVal_orIn (N + ko) w _ hk_w (by simp)
                                    have h2 : circuitFun N D (fun i => decide (i = w)) = true := h1
                                    rw [hDeval, hSingle_false w] at h2; cases h2
                                  have hko_kept : ko ∈ kept := by
                                    rw [hkept_mem]; exact ⟨by omega, fun h => hout_g (by omega), hko_ne_hu, hko_nKdel⟩
                                  rw [hko, hremap_kept_mem ko hko_kept]
                                  exact Nat.add_lt_add_left (List.idxOf_lt_length_of_mem hko_kept) N)]
                            by_cases hU_pq : s(p, q) ∈ Ustar G D
                            · have hw_pq : p = w ∨ q = w := by
                                by_contra! hnw
                                obtain ⟨a, ha, p0, q0, hspq, _, b_a, hreach_a, hgval, _, hside⟩ := hU_g s(p, q) hU_pq
                                rw [hg_iff] at hgval
                                rcases hgval with ⟨⟨p1, hp1, hp1_eq⟩, ⟨q1, hq1, hq1_eq⟩⟩
                                have hp1' : p1 = p ∨ p1 = q := by
                                  have h0 : p1 = p0 ∨ p1 = q0 := by unfold pairInput at hp1_eq; simpa using hp1_eq
                                  rcases Sym2.eq_iff.mp hspq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
                                  · exact h0
                                  · rcases h0 with rfl | rfl <;> simp
                                have hq1' : q1 = p ∨ q1 = q := by
                                  have h0 : q1 = p0 ∨ q1 = q0 := by unfold pairInput at hq1_eq; simpa using hq1_eq
                                  rcases Sym2.eq_iff.mp hspq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
                                  · exact h0
                                  · rcases h0 with rfl | rfl <;> simp
                                have hS01 : (p ∈ S0 ∧ q ∈ S1) ∨ (q ∈ S0 ∧ p ∈ S1) := by
                                  rcases hp1' with hp1p | hp1q <;> rcases hq1' with hq1p | hq1q
                                  · exact absurd ((hI_iff p).mp (Finset.mem_inter.mpr ⟨hp1p ▸ hp1, hq1p ▸ hq1⟩)) hnw.1
                                  · exact Or.inl ⟨hp1p ▸ hp1, hq1q ▸ hq1⟩
                                  · exact Or.inr ⟨hp1q ▸ hp1, hq1p ▸ hq1⟩
                                  · exact absurd ((hI_iff q).mp (Finset.mem_inter.mpr ⟨hp1q ▸ hp1, hq1q ▸ hq1⟩)) hnw.2
                                have hS_pq : (p ∈ Su ∧ q ∈ Sv) ∨ (q ∈ Su ∧ p ∈ Sv) := by
                                  fin_cases b_u
                                  · exact hS01
                                  · rcases hS01 with ⟨hp0, hq1⟩ | ⟨hq0, hp1⟩
                                    · exact Or.inr ⟨hq1, hp0⟩
                                    · exact Or.inl ⟨hp1, hq0⟩
                                have hwmax_pq : p ∈ wmax G D g ∨ q ∈ wmax G D g := by
                                  rcases hside with hp0s | hq0s
                                  · have h1 := hSide_wmax a ha b_a hreach_a p0 hp0s
                                    rcases Sym2.eq_iff.mp hspq with ⟨hpp0, _⟩ | ⟨_, hqp0⟩
                                    · exact Or.inl (hpp0 ▸ h1)
                                    · exact Or.inr (hqp0 ▸ h1)
                                  · have h1 := hSide_wmax a ha b_a hreach_a q0 hq0s
                                    rcases Sym2.eq_iff.mp hspq with ⟨_, hqq0⟩ | ⟨hpq0, _⟩
                                    · exact Or.inr (hqq0 ▸ h1)
                                    · exact Or.inl (hpq0 ▸ h1)
                                rcases hS_pq with ⟨hpSu, hqSv⟩ | ⟨hqSu, hpSv⟩
                                · rcases hwmax_pq with hpw | hqw
                                  · have hpu0 : p = u0 := hWu_eq p hpw hpSu
                                    exact hpq_rem (Or.inl ⟨hpu0, Finset.mem_filter.mpr ⟨hqSv, hnw.2,
                                      by rw [← hpu0]; exact hU_pq⟩⟩)
                                  · exact hWv_empty q hqw hqSv
                                · rcases hwmax_pq with hpw | hqw
                                  · exact hWv_empty p hpw hpSv
                                  · have hqu0 : q = u0 := hWu_eq q hqw hqSu
                                    exact hpq_rem (Or.inr ⟨hqu0, Finset.mem_filter.mpr ⟨hpSv, hnw.1,
                                      by rw [← hqu0, Sym2.eq_swap]; exact hU_pq⟩⟩)
                              have hxw : x w = true := by rcases hw_pq with rfl | rfl <;> assumption
                              have hAgreeW_kept : ∀ i, i < N + D.gates.length →
                                  (i ≠ N + hu ∧ ∀ k ∈ K_del, i ≠ N + k) →
                                  wireVal i x = true → wireVal_st gates0 (remap_kept i) x = true := by
                                intro i
                                induction i using Nat.strong_induction_on with
                                | ind i ih =>
                                  intro hi ⟨hne_hu, hne_kd⟩ hval
                                  by_cases hiN : i < N
                                  · rw [hremap_kept_lt_N i hiN, hwire_lt gates0 i hiN x]
                                    rwa [wireVal_lt ⟨i, hiN⟩ x] at hval
                                  · by_cases hi_g : i = N + g
                                    · rw [hi_g, hremap_kept_g]
                                      rwa [hwire_lt gates0 w.1 w.isLt x]
                                    · obtain ⟨k, rfl⟩ : ∃ k, i = N + k := ⟨i - N, by omega⟩
                                      have hk_len : k < D.gates.length := by omega
                                      have hk_kept : k ∈ kept := by
                                        rw [hkept_mem]; exact ⟨hk_len, fun h => hi_g (by omega),
                                          fun h => hne_hu (by omega), fun hk' => hne_kd k hk' rfl⟩
                                      have hidx_gs : kept.idxOf k < gates0.length := by
                                        rw [hgates0_len]; exact List.idxOf_lt_length_of_mem hk_kept
                                      have hget := hgates0_idxOf k hk_kept hidx_gs
                                      rw [hremap_kept_mem k hk_kept, hwire_gate gates0 (kept.idxOf k) hidx_gs x, hget]
                                      rw [wireVal_gate k hk_len x] at hval
                                      let a0 := opnd D k 0
                                      let a1 := opnd D k 1
                                      have ha01 : (gateAt D k).inputs = [a0, a1] := hgateAt_D_inputs k hk_len
                                      have ha0_lt : a0 < N + k := hopnd_D_lt k hk_len 0
                                      have ha1_lt : a1 < N + k := hopnd_D_lt k hk_len 1
                                      have hra0 := hremap_kept_lt k hk_kept a0 ha0_lt (hKept_no_del k hk_kept a0 (hopnd_D_mem k hk_len 0))
                                      have hra1 := hremap_kept_lt k hk_kept a1 ha1_lt (hKept_no_del k hk_kept a1 (hopnd_D_mem k hk_len 1))
                                      have h0eq : opnd D k 0 = a0 := rfl
                                      have h1eq : opnd D k 1 = a1 := rfl
                                      rw [ha01]
                                      rw [h0eq, h1eq] at hval
                                      simp only [List.map_cons, List.map_nil, hra0, hra1, ↓reduceIte] at hval ⊢
                                      rcases hDAO.1 (gateAt D k) (hgateAt_D_mem k hk_len) with hop | hop
                                      · rw [hop] at hval ⊢
                                        simp only [GateOp.eval, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at hval ⊢
                                        exact ⟨ih a0 ha0_lt (Nat.lt_trans ha0_lt hi)
                                            (hKept_no_del k hk_kept a0 (by rw [ha01]; simp)) hval.1,
                                          ih a1 ha1_lt (Nat.lt_trans ha1_lt hi)
                                            (hKept_no_del k hk_kept a1 (by rw [ha01]; simp)) hval.2⟩
                                      · rw [hop] at hval ⊢
                                        simp only [GateOp.eval, List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true] at hval ⊢
                                        rcases hval with h0 | h1
                                        · exact Or.inl (ih a0 ha0_lt (Nat.lt_trans ha0_lt hi)
                                            (hKept_no_del k hk_kept a0 (by rw [ha01]; simp)) h0)
                                        · exact Or.inr (ih a1 ha1_lt (Nat.lt_trans ha1_lt hi)
                                            (hKept_no_del k hk_kept a1 (by rw [ha01]; simp)) h1)
                              have hD_true : wireVal D.output x = true := by
                                change circuitFun N D x = true; rw [hDeval]; exact hgf
                              have hout_ne_hu : D.output ≠ N + hu := by
                                intro heq
                                have h1 : wireVal D.output (fun i => decide (i = w)) = true := by
                                  rw [heq]; exact wireVal_orIn (N + hu) w _ (by rw [← hhu_eq]; exact hw_Su) (by simp)
                                have h2 : circuitFun N D (fun i => decide (i = w)) = true := h1
                                rw [hDeval, hSingle_false w] at h2; cases h2
                              have hout_ne_kd : ∀ k ∈ K_del, D.output ≠ N + k := by
                                intro k hk heq
                                have hk_w := (Finset.mem_filter.mp (Finset.mem_filter.mp hk).1).2.2
                                have h1 : wireVal D.output (fun i => decide (i = w)) = true := by
                                  rw [heq]; exact wireVal_orIn (N + k) w _ hk_w (by simp)
                                have h2 : circuitFun N D (fun i => decide (i = w)) = true := h1
                                rw [hDeval, hSingle_false w] at h2; cases h2
                              exact hAgreeW_kept D.output hout_lt ⟨hout_ne_hu, hout_ne_kd⟩ hD_true
                            · have hstar : s(p, q) ∈ PEqualNP.TopForm.starEdges G D := by
                                have hedges : s(p, q) ∈ G.edgeFinset := by
                                  simpa [SimpleGraph.mem_edgeFinset] using hadj
                                by_contra hns; exact hU_pq (Finset.mem_sdiff.mpr ⟨hedges, hns⟩)
                              simp only [PEqualNP.TopForm.starEdges, Finset.mem_biUnion, Finset.mem_image,
                                Finset.mem_product, Prod.exists] at hstar
                              obtain ⟨a, ha, p0, q0, ⟨hp0, hq0⟩, hspq⟩ := hstar
                              have ha' := ha
                              simp only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range] at ha'
                              have hOrIn_gates0 : ∀ i z, i < N + D.gates.length → z ∈ orIn N D i → x z = true →
                                  (¬ OrReaches N D i hu) → (∀ k ∈ K_del, ¬ OrReaches N D i k) →
                                  wireVal_st gates0 (remap_kept i) x = true := by
                                intro i
                                induction i using Nat.strong_induction_on with
                                | ind i ih =>
                                  intro z hi hzi hxz hnhu hnkd
                                  by_cases hiN : i < N
                                  · rw [hremap_kept_lt_N i hiN, hwire_lt gates0 i hiN x]
                                    have h_in : ⟨i, hiN⟩ ∈ orIn N D i := by
                                      have hno : ¬ ∃ g' < D.gates.length, (gateAt D g').op = GateOp.and ∧ OrReaches N D i g' :=
                                        fun ⟨g', _, _, hr⟩ => absurd (orReaches_le i g' hr) (by omega)
                                      obtain ⟨v, hv_in, hv_eq⟩ := (wireVal_orIn_iff_no_and i (fun j => decide (j = ⟨i, hiN⟩)) hno).mp
                                        (by rw [wireVal_lt ⟨i, hiN⟩]; simp)
                                      have hv_eq' : v = ⟨i, hiN⟩ := by simpa using hv_eq
                                      rwa [← hv_eq']
                                    have hz_eq := Finset.card_le_one.mp (hOrIn_lt i hiN) z hzi ⟨i, hiN⟩ h_in
                                    rwa [← hz_eq]
                                  · obtain ⟨k, rfl⟩ : ∃ k, i = N + k := ⟨i - N, by omega⟩
                                    have hk_len : k < D.gates.length := by omega
                                    obtain ⟨_, hkop, w_in, hw_mem, hw_lt, hzw⟩ := (hOrIn_gate k z).mp hzi
                                    have hk_ne_g : k ≠ g := by
                                      intro heq; subst heq; rw [hg_op] at hkop; cases hkop
                                    have hk_ne_hu : k ≠ hu := fun heq =>
                                      hnhu (heq ▸ hOrReaches_self k hk_len)
                                    have hk_nkd : k ∉ K_del := fun hm =>
                                      hnkd k hm (hOrReaches_self k hk_len)
                                    have hk_kept : k ∈ kept := by
                                      rw [hkept_mem]; exact ⟨hk_len, hk_ne_g, hk_ne_hu, hk_nkd⟩
                                    have hnhu_w : ¬ OrReaches N D w_in hu := fun hr =>
                                      hnhu (hOrReaches_step (N + k) k hu (hOrReaches_self k hk_len) hkop w_in hw_mem hw_lt hr)
                                    have hnkd_w : ∀ k' ∈ K_del, ¬ OrReaches N D w_in k' := fun k' hk' hr =>
                                      hnkd k' hk' (hOrReaches_step (N + k) k k' (hOrReaches_self k hk_len) hkop w_in hw_mem hw_lt hr)
                                    have hih := ih w_in hw_lt z (Nat.lt_trans hw_lt hi) hzw hxz hnhu_w hnkd_w
                                    have hidx_gs : kept.idxOf k < gates0.length := by
                                      rw [hgates0_len]; exact List.idxOf_lt_length_of_mem hk_kept
                                    have hget := hgates0_idxOf k hk_kept hidx_gs
                                    rw [hremap_kept_mem k hk_kept, hwire_gate gates0 (kept.idxOf k) hidx_gs x, hget, hkop]
                                    simp only [GateOp.eval, List.any_map, List.any_eq_true]
                                    refine ⟨w_in, hw_mem, ?_⟩
                                    have hlt_w := hremap_kept_lt k hk_kept w_in hw_lt (hKept_no_del k hk_kept w_in hw_mem)
                                    simp [hlt_w, hih]
                              have hlen2a : (gateAt D a).inputs.length = 2 := by
                                apply hDAO.2.2; unfold gateAt; simp [List.getD_eq_getElem?_getD, ha'.1]
                              have hopnd_ok : ∀ b : Fin 2, ∀ z ∈ PEqualNP.TopForm.side D a b, x z = true →
                                  wireVal_st gates0 (remap_kept (opnd D a b)) x = true := by
                                intro b z hz hxz
                                have hb_lt : opnd D a b < N + a := hDAO.2.1 a ha'.1 _ (by
                                  unfold opnd; have hb : (b : ℕ) < (gateAt D a).inputs.length := by omega
                                  simp [hb, List.getElem_mem])
                                apply hOrIn_gates0 (opnd D a b) z (by omega) hz hxz
                                · intro hr; exact hNotUses_hu ⟨a, ha, b, hr⟩
                                · intro k hk hr; exact (Finset.mem_filter.mp hk).2 ⟨a, ha, b, hr⟩
                              have hxp0 : x p0 = true := by
                                rcases Sym2.eq_iff.mp hspq with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> assumption
                              have hxq0 : x q0 = true := by
                                rcases Sym2.eq_iff.mp hspq with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> assumption
                              have hval0 := hopnd_ok 0 p0 hp0 hxp0
                              have hval1 := hopnd_ok 1 q0 hq0 hxq0
                              have ha_ne_g : a ≠ g := fun heq => hg_nbel (heq ▸ ha'.2.2)
                              have ha_ne_hu : a ≠ hu := by
                                intro heq; subst heq; have haop := ha'.2.1; rw [hhu_op] at haop; cases haop
                              have ha_nkd : a ∉ K_del := by
                                intro hm; exact hk_noAnd a hm ⟨a, ha'.1, ha'.2.1, hOrReaches_self a ha'.1⟩
                              have ha_kept : a ∈ kept := by
                                rw [hkept_mem]; exact ⟨ha'.1, ha_ne_g, ha_ne_hu, ha_nkd⟩
                              have hval_a : wireVal_st gates0 (remap_kept (N + a)) x = true := by
                                have hidx_gs : kept.idxOf a < gates0.length := by
                                  rw [hgates0_len]; exact List.idxOf_lt_length_of_mem ha_kept
                                have hget := hgates0_idxOf a ha_kept hidx_gs
                                rw [hremap_kept_mem a ha_kept, hwire_gate gates0 (kept.idxOf a) hidx_gs x, hget, ha'.2.1]
                                have ha01 : (gateAt D a).inputs = [opnd D a 0, opnd D a 1] := hgateAt_D_inputs a ha'.1
                                rw [ha01]
                                have hra0 := hremap_kept_lt a ha_kept (opnd D a 0) (hopnd_D_lt a ha'.1 0)
                                  (hKept_no_del a ha_kept _ (hopnd_D_mem a ha'.1 0))
                                have hra1 := hremap_kept_lt a ha_kept (opnd D a 1) (hopnd_D_lt a ha'.1 1)
                                  (hKept_no_del a ha_kept _ (hopnd_D_mem a ha'.1 1))
                                simp only [GateOp.eval, List.map_cons, List.map_nil, hra0, hra1, ↓reduceIte,
                                  List.all_cons, List.all_nil, Bool.and_true, hval0, hval1]
                                rfl
                              have hLift : ∀ i, OrReaches N D i a →
                                  wireVal_st gates0 (remap_kept i) x = true := by
                                intro i hi
                                have hri := (orReaches_reach a i hi).1
                                induction hri using Relation.ReflTransGen.head_induction_on with
                                | refl => exact hval_a
                                | @head _ v_i hstep hrest ih =>
                                  rcases hstep with ⟨k, hk_len, rfl, hkop, hv_mem, hv_lt⟩
                                  have hk_ne_g : k ≠ g := fun heq => by rw [heq, hg_op] at hkop; cases hkop
                                  have hk_ne_hu' : k ≠ hu := fun heq => by
                                    apply hNoAnd_g b_u; refine ⟨a, ha'.1, ha'.2.1, ?_⟩
                                    rw [hhu_eq, ← heq]
                                    exact hOrReaches_step (N + k) k a (hOrReaches_self k hk_len) hkop v_i hv_mem hv_lt
                                      (reach_orReaches ‹_› a rfl ha'.1)
                                  have hk_nkd : k ∉ K_del := fun hm =>
                                    hk_noAnd k hm ⟨a, ha'.1, ha'.2.1,
                                      hOrReaches_step (N + k) k a (hOrReaches_self k hk_len) hkop v_i hv_mem hv_lt
                                        (reach_orReaches ‹_› a rfl ha'.1)⟩
                                  have hk_kept : k ∈ kept := by
                                    rw [hkept_mem]; exact ⟨hk_len, hk_ne_g, hk_ne_hu', hk_nkd⟩
                                  have hidx_gs : kept.idxOf k < gates0.length := by
                                    rw [hgates0_len]; exact List.idxOf_lt_length_of_mem hk_kept
                                  have hget := hgates0_idxOf k hk_kept hidx_gs
                                  rw [hremap_kept_mem k hk_kept, hwire_gate gates0 (kept.idxOf k) hidx_gs x, hget, hkop]
                                  simp only [GateOp.eval, List.any_map, List.any_eq_true]
                                  refine ⟨v_i, hv_mem, ?_⟩
                                  have hlt_v := hremap_kept_lt k hk_kept v_i hv_lt (hKept_no_del k hk_kept v_i hv_mem)
                                  simp [hlt_v, ih (reach_orReaches hrest a rfl ha'.1)]
                              exact hLift D.output (hTop_orReaches_out a ha)
                          rw [hkept_t, Bool.true_or]
                    have hle := hDleast.2.2 D' hD'_AO2 hD'_eval
                    change D.gates.length ≤ D'.gates.length at hle
                    omega
                by_cases hExW0 : ∃ u ∈ W0, ∃ v ∈ S1 \ {w}, G.Adj u v
                · obtain ⟨u0, hu0, v0, hv0, hadj⟩ := hExW0
                  have hu0_wmax : u0 ∈ wmax G D g := (Finset.mem_filter.mp hu0).1
                  have hu0_S0 : u0 ∈ S0 := (Finset.mem_filter.mp hu0).2
                  have hv0_S1 : v0 ∈ S1 := (Finset.mem_sdiff.mp hv0).1
                  have hv0_ne_w : v0 ≠ w := by simpa using (Finset.mem_sdiff.mp hv0).2
                  have hS1_ge2 : 2 ≤ S1.card :=
                    Finset.one_lt_card.mpr ⟨w, hw_S1, v0, hv0_S1, hv0_ne_w.symm⟩
                  have hW0_le1 := hW0_card hS1_ge2
                  have hW1_e : W1 = ∅ := hW01_empty.resolve_left (Finset.nonempty_iff_ne_empty.mp ⟨u0, hu0⟩)
                  exact False.elim (hOneSide_contra 0 u0 hu0_wmax hu0_S0 ⟨v0, hv0, hadj⟩
                    (fun u hu_w hu_S0 => Finset.card_le_one.mp hW0_le1 u (Finset.mem_filter.mpr ⟨hu_w, hu_S0⟩) u0 hu0)
                    (fun v hv_w hv_S1 => by
                      have hmem : v ∈ W1 := Finset.mem_filter.mpr ⟨hv_w, hv_S1⟩
                      rw [hW1_e] at hmem; exact absurd hmem (Finset.notMem_empty _)))
                · by_cases hExW1 : ∃ v ∈ W1, ∃ u ∈ S0 \ {w}, G.Adj v u
                  · obtain ⟨v0, hv0, u0, hu0, hadj⟩ := hExW1
                    have hv0_wmax : v0 ∈ wmax G D g := (Finset.mem_filter.mp hv0).1
                    have hv0_S1 : v0 ∈ S1 := (Finset.mem_filter.mp hv0).2
                    have hu0_S0 : u0 ∈ S0 := (Finset.mem_sdiff.mp hu0).1
                    have hu0_ne_w : u0 ≠ w := by simpa using (Finset.mem_sdiff.mp hu0).2
                    have hS0_ge2 : 2 ≤ S0.card :=
                      Finset.one_lt_card.mpr ⟨w, hw_S0, u0, hu0_S0, hu0_ne_w.symm⟩
                    have hW1_le1 := hW1_card hS0_ge2
                    have hW0_e : W0 = ∅ := hW01_empty.resolve_right (Finset.nonempty_iff_ne_empty.mp ⟨v0, hv0⟩)
                    exact False.elim (hOneSide_contra 1 v0 hv0_wmax hv0_S1 ⟨u0, hu0, hadj⟩
                      (fun v hv_w hv_S1 => Finset.card_le_one.mp hW1_le1 v (Finset.mem_filter.mpr ⟨hv_w, hv_S1⟩) v0 hv0)
                      (fun u hu_w hu_S0 => by
                        have hmem : u ∈ W0 := Finset.mem_filter.mpr ⟨hu_w, hu_S0⟩
                        rw [hW0_e] at hmem; exact absurd hmem (Finset.notMem_empty _)))
                  · exact False.elim (hDelete_contra
                      (fun u hu v hv hU => hExW0 ⟨u, hu, v, hv, SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp hU).1⟩)
                      (fun v hv u hu hU => hExW1 ⟨v, hv, u, hu, (SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp hU).1).symm⟩))
          · have hDisj : Disjoint S0 S1 := Finset.disjoint_iff_inter_eq_empty.mpr
              (Finset.not_nonempty_iff_eq_empty.mp hInter)
            have hU_S01 : ∀ e ∈ Ustar G D, ∃ u ∈ S0, ∃ v ∈ S1, e = s(u, v) ∧ u ≠ v ∧
                (u ∈ W0 ∨ v ∈ W1) := by
              intro e heU
              obtain ⟨a, ha, p, q, rfl, hpq, b_a, hreach, hgval, _, hside⟩ := hU_g e heU
              rw [hg_iff] at hgval
              rcases hgval with ⟨⟨p0, hp0, hp0_eq⟩, ⟨q1, hq1, hq1_eq⟩⟩
              have hp0' : p0 = p ∨ p0 = q := by simpa [pairInput] using hp0_eq
              have hq1' : q1 = p ∨ q1 = q := by simpa [pairInput] using hq1_eq
              have hS01 : (p ∈ S0 ∧ q ∈ S1) ∨ (q ∈ S0 ∧ p ∈ S1) := by
                rcases hp0' with rfl | rfl <;> rcases hq1' with rfl | rfl
                · exact False.elim (Finset.disjoint_left.mp hDisj hp0 hq1)
                · exact Or.inl ⟨hp0, hq1⟩
                · exact Or.inr ⟨hp0, hq1⟩
                · exact False.elim (Finset.disjoint_left.mp hDisj hp0 hq1)
              have hwmax_pq : p ∈ wmax G D g ∨ q ∈ wmax G D g := by
                rcases hside with hp_s | hq_s
                · exact Or.inl (hSide_wmax a ha b_a hreach p hp_s)
                · exact Or.inr (hSide_wmax a ha b_a hreach q hq_s)
              rcases hS01 with ⟨hp0, hq1⟩ | ⟨hq0, hp1⟩
              · refine ⟨p, hp0, q, hq1, rfl, hpq, ?_⟩
                rcases hwmax_pq with hpw | hqw
                · exact Or.inl (Finset.mem_filter.mpr ⟨hpw, hp0⟩)
                · exact Or.inr (Finset.mem_filter.mpr ⟨hqw, hq1⟩)
              · refine ⟨q, hq0, p, hp1, Sym2.eq_swap, hpq.symm, ?_⟩
                rcases hwmax_pq with hpw | hqw
                · exact Or.inr (Finset.mem_filter.mpr ⟨hpw, hp1⟩)
                · exact Or.inl (Finset.mem_filter.mpr ⟨hqw, hq0⟩)
            -- Case 1: S0 ∩ S1 = ∅
            by_cases hS0_le1 : S0.card ≤ 1
            · obtain ⟨e0, he0⟩ := hU
              obtain ⟨x0, hx0, _, _, _, _, _⟩ := hU_S01 e0 he0
              apply hOneCover x0 1
              intro e he
              obtain ⟨u, hu, v, hv, rfl, huv, _⟩ := hU_S01 e he
              have hux : u = x0 := Finset.card_le_one.mp hS0_le1 u hu x0 hx0
              subst hux
              exact ⟨Sym2.mem_mk_left _ _, v, hv, huv.symm, rfl⟩
            · by_cases hS1_le1 : S1.card ≤ 1
              · obtain ⟨e0, he0⟩ := hU
                obtain ⟨_, _, x1, hx1, _, _, _⟩ := hU_S01 e0 he0
                apply hOneCover x1 0
                intro e he
                obtain ⟨u, hu, v, hv, rfl, huv, _⟩ := hU_S01 e he
                have hvx : v = x1 := Finset.card_le_one.mp hS1_le1 v hv x1 hx1
                subst hvx
                exact ⟨Sym2.mem_mk_right _ _, u, hu, huv, Sym2.eq_swap⟩
              · have hS0_ge2 : 2 ≤ S0.card := by omega
                have hS1_ge2 : 2 ≤ S1.card := by omega
                have hW0_le1 := hW0_card hS1_ge2
                have hW1_le1 := hW1_card hS0_ge2
                let W0' := W0.filter fun u => ∃ v ∈ S1, v ∉ W1 ∧ s(u, v) ∈ Ustar G D
                let W1' := W1.filter fun v => ∃ u ∈ S0, u ∉ W0 ∧ s(u, v) ∈ Ustar G D
                have hW0'_mem : ∀ x, x ∈ W0' → x ∈ W0 ∧ ∃ v ∈ S1, v ∉ W1 ∧ s(x, v) ∈ Ustar G D :=
                  fun _ hx => Finset.mem_filter.mp hx
                have hW1'_mem : ∀ x, x ∈ W1' → x ∈ W1 ∧ ∃ u ∈ S0, u ∉ W0 ∧ s(u, x) ∈ Ustar G D :=
                  fun _ hx => Finset.mem_filter.mp hx
                by_cases hW0' : W0' = ∅
                · by_cases hW1' : W1' = ∅
                  · -- Both W0' and W1' empty => every e ∈ U is in s(W0, W1), so U.card ≤ 1
                    obtain ⟨e0, he0⟩ := hU
                    obtain ⟨u0, hu0, v0, hv0, he0eq, huv0, hu0w | hv0w⟩ := hU_S01 e0 he0
                    · have hv0_W1 : v0 ∈ W1 := by
                        by_contra hn
                        have : u0 ∈ W0' := Finset.mem_filter.mpr ⟨hu0w, v0, hv0, hn, he0eq ▸ he0⟩
                        rw [hW0'] at this; exact absurd this (Finset.notMem_empty _)
                      have hu0_W0 : u0 ∈ W0 := hu0w
                      have hU_eq1 : ∀ e ∈ Ustar G D, u0 ∈ e ∧
                          ∃ y ∈ orIn N D (opnd D g 1), y ≠ u0 ∧ e = s(u0, y) := by
                        intro e he
                        obtain ⟨u, hu, v, hv, rfl, huv, hw⟩ := hU_S01 e he
                        have hsub_W0 : u ∈ W0 := by
                          rcases hw with huw | hvw
                          · exact huw
                          · by_contra hn
                            have : v ∈ W1' := Finset.mem_filter.mpr ⟨hvw, u, hu, hn, he⟩
                            rw [hW1'] at this; exact absurd this (Finset.notMem_empty _)
                        have heq : u = u0 := Finset.card_le_one.mp hW0_le1 u hsub_W0 u0 hu0_W0
                        subst heq
                        exact ⟨Sym2.mem_mk_left _ _, v, hv, huv.symm, rfl⟩
                      exact hOneCover u0 1 hU_eq1
                    · have hu0_W0 : u0 ∈ W0 := by
                        by_contra hn
                        have : v0 ∈ W1' := Finset.mem_filter.mpr ⟨hv0w, u0, hu0, hn, he0eq ▸ he0⟩
                        rw [hW1'] at this; exact absurd this (Finset.notMem_empty _)
                      have hv0_W1 : v0 ∈ W1 := hv0w
                      have hU_eq1 : ∀ e ∈ Ustar G D, v0 ∈ e ∧
                          ∃ y ∈ orIn N D (opnd D g 0), y ≠ v0 ∧ e = s(v0, y) := by
                        intro e he
                        obtain ⟨u, hu, v, hv, rfl, huv, hw⟩ := hU_S01 e he
                        have hsub_W1 : v ∈ W1 := by
                          rcases hw with huw | hvw
                          · by_contra hn
                            have : u ∈ W0' := Finset.mem_filter.mpr ⟨huw, v, hv, hn, he⟩
                            rw [hW0'] at this; exact absurd this (Finset.notMem_empty _)
                          · exact hvw
                        have heq : v = v0 := Finset.card_le_one.mp hW1_le1 v hsub_W1 v0 hv0_W1
                        subst heq
                        exact ⟨Sym2.mem_mk_right _ _, u, hu, huv, Sym2.eq_swap⟩
                      exact hOneCover v0 0 hU_eq1
                  · -- W0' = ∅, W1' ≠ ∅ -> W1 covers all U
                    obtain ⟨v0, hv0'⟩ := Finset.nonempty_iff_ne_empty.mpr hW1'
                    have hv0 : v0 ∈ W1 := (Finset.mem_filter.mp hv0').1
                    apply hOneCover v0 0
                    intro e he
                    obtain ⟨u, hu, v, hv, rfl, huv, hw⟩ := hU_S01 e he
                    have hvW1 : v ∈ W1 := by
                      rcases hw with huw | hvw
                      · by_contra hn
                        have : u ∈ W0' := Finset.mem_filter.mpr ⟨huw, v, hv, hn, he⟩
                        rw [hW0'] at this; exact absurd this (Finset.notMem_empty _)
                      · exact hvw
                    have heq : v = v0 := Finset.card_le_one.mp hW1_le1 v hvW1 v0 hv0
                    subst heq
                    exact ⟨Sym2.mem_mk_right _ _, u, hu, huv, Sym2.eq_swap⟩
                · by_cases hW1' : W1' = ∅
                  · -- W0' ≠ ∅, W1' = ∅ -> W0 covers all U
                    obtain ⟨u0, hu0'⟩ := Finset.nonempty_iff_ne_empty.mpr hW0'
                    have hu0 : u0 ∈ W0 := (Finset.mem_filter.mp hu0').1
                    apply hOneCover u0 1
                    intro e he
                    obtain ⟨u, hu, v, hv, rfl, huv, hw⟩ := hU_S01 e he
                    have huW0 : u ∈ W0 := by
                      rcases hw with huw | hvw
                      · exact huw
                      · by_contra hn
                        have : v ∈ W1' := Finset.mem_filter.mpr ⟨hvw, u, hu, hn, he⟩
                        rw [hW1'] at this; exact absurd this (Finset.notMem_empty _)
                    have heq : u = u0 := Finset.card_le_one.mp hW0_le1 u huW0 u0 hu0
                    subst heq
                    exact ⟨Sym2.mem_mk_left _ _, v, hv, huv.symm, rfl⟩
                  · -- Both W0' ≠ ∅ and W1' ≠ ∅
                    obtain ⟨u0, hu0'⟩ := Finset.nonempty_iff_ne_empty.mpr hW0'
                    obtain ⟨v0, hv0'⟩ := Finset.nonempty_iff_ne_empty.mpr hW1'
                    have hu0 : u0 ∈ W0 := (Finset.mem_filter.mp hu0').1
                    have hv0 : v0 ∈ W1 := (Finset.mem_filter.mp hv0').1
                    have hu0_ne_v0 : u0 ≠ v0 := fun heq => hW0_nS1 u0 hu0 (heq ▸ (Finset.mem_filter.mp hv0).2)
                    have hU_cov2 : ∀ e ∈ Ustar G D, u0 ∈ e ∨ v0 ∈ e := by
                      intro e he
                      obtain ⟨u, _, v, _, rfl, _, hw⟩ := hU_S01 e he
                      rcases hw with huw | hvw
                      · left; rw [Finset.card_le_one.mp hW0_le1 u huw u0 hu0]; exact Sym2.mem_mk_left _ _
                      · right; rw [Finset.card_le_one.mp hW1_le1 v hvw v0 hv0]; exact Sym2.mem_mk_right _ _
                    let Nu0 : Finset (Fin N) := S1.filter fun v => s(u0, v) ∈ Ustar G D
                    let Nv0 : Finset (Fin N) := S0.filter fun u => s(u, v0) ∈ Ustar G D
                    have hNu0_Nv0_disj : Disjoint Nu0 Nv0 := by
                      rw [Finset.disjoint_left]
                      intro w hw1 hw2
                      exact Finset.disjoint_left.mp hDisj (Finset.mem_filter.mp hw2).1 (Finset.mem_filter.mp hw1).1
                    let S_both := Nu0 ∪ Nv0
                    let W_both : Finset ℕ := {opnd D g 0, opnd D g 1}
                    have hS_both_sub : S_both ⊆ W_both.biUnion (fun w => orIn N D w) := by
                      intro w hw
                      rcases Finset.mem_union.mp hw with hw1 | hw2
                      · exact Finset.mem_biUnion.mpr ⟨opnd D g 1, by simp [W_both], (Finset.mem_filter.mp hw1).1⟩
                      · exact Finset.mem_biUnion.mpr ⟨opnd D g 0, by simp [W_both], (Finset.mem_filter.mp hw2).1⟩
                    have hS_both_lam : ∀ h ∈ lam G D, (S_both ∩ orIn N D (N + h)).card ≤ 1 := by
                      intro h hh
                      have hlam' := hh
                      simp only [lam, Finset.mem_filter] at hlam'
                      rcases hlam' with ⟨_, _, _, ah, hah, bh, hcard1h, hreachh⟩
                      obtain ⟨zh, hzh⟩ := Finset.card_eq_one.mp hcard1h
                      have hzh_mem : zh ∈ PEqualNP.TopForm.side D ah (1 - bh) := by
                        rw [hzh]; exact Finset.mem_singleton_self zh
                      have hAdjZ : ∀ w ∈ orIn N D (N + h), G.Adj zh w := by
                        intro w hw
                        have hw_side := hOrIn_mono (opnd D ah bh) h w hreachh hw
                        fin_cases bh
                        · exact (hTop_adj ah hah w hw_side zh hzh_mem).1.symm
                        · exact (hTop_adj ah hah zh hzh_mem w hw_side).1
                      obtain ⟨col, hcol⟩ := hBip
                      have hadj_uv : G.Adj u0 v0 := hW0_adj_S1 u0 hu0 v0 (Finset.mem_filter.mp hv0).2
                      have hcol_uv : col u0 ≠ col v0 := hcol hadj_uv
                      by_cases hcz : col zh = col u0
                      · have hsub : S_both ∩ orIn N D (N + h) ⊆
                            (orIn N D (N + h)).filter fun w => s(u0, w) ∈ Ustar G D := by
                          intro w hw
                          rw [Finset.mem_inter] at hw
                          refine Finset.mem_filter.mpr ⟨hw.2, ?_⟩
                          rcases Finset.mem_union.mp hw.1 with hw1 | hw2
                          · exact (Finset.mem_filter.mp hw1).2
                          · exfalso
                            have hadj_w_v0 : G.Adj w v0 := hW1_adj_S0 v0 hv0 w (Finset.mem_filter.mp hw2).1
                            have hadj_zh_w : G.Adj zh w := hAdjZ w hw.2
                            have hcw1 : col zh ≠ col w := hcol hadj_zh_w
                            have hcw2 : col w ≠ col v0 := hcol hadj_w_v0
                            have : col u0 = col v0 := by omega
                            exact hcol_uv this
                        exact le_trans (Finset.card_le_card hsub) (hLam_bound h hh u0)
                      · have hsub : S_both ∩ orIn N D (N + h) ⊆
                            (orIn N D (N + h)).filter fun w => s(v0, w) ∈ Ustar G D := by
                          intro w hw
                          rw [Finset.mem_inter] at hw
                          refine Finset.mem_filter.mpr ⟨hw.2, ?_⟩
                          rcases Finset.mem_union.mp hw.1 with hw1 | hw2
                          · exfalso
                            have hadj_u0_w : G.Adj u0 w := hW0_adj_S1 u0 hu0 w (Finset.mem_filter.mp hw1).1
                            have hadj_zh_w : G.Adj zh w := hAdjZ w hw.2
                            have hcw1 : col zh ≠ col w := hcol hadj_zh_w
                            have hcw2 : col u0 ≠ col w := hcol hadj_u0_w
                            have : col zh = col u0 := by omega
                            exact hcz this
                          · rw [Sym2.eq_swap]; exact (Finset.mem_filter.mp hw2).2
                        exact le_trans (Finset.card_le_card hsub) (hLam_bound h hh v0)
                    have hGML_both := hGML W_both S_both hS_both_sub hS_both_lam
                    have hW_both_card : W_both.card ≤ 2 := Finset.card_le_two
                    let B_both := (orN G D \ lam G D).filter fun h =>
                      (∃ w ∈ W_both, OrReaches N D w h) ∧ 2 ≤ (S_both ∩ orIn N D (N + h)).card
                    have hS_both_le : Nu0.card + Nv0.card ≤ 2 + B_both.card := by
                      have h1 : S_both.card = Nu0.card + Nv0.card := Finset.card_union_of_disjoint hNu0_Nv0_disj
                      have h2 : S_both.card ≤ W_both.card + B_both.card := hGML_both
                      omega
                    have hU_sub_both : Ustar G D ⊆
                        (Nu0.image fun v => s(u0, v)) ∪ (Nv0.image fun u => s(u, v0)) := by
                      intro e he
                      obtain ⟨u, hu, v, hv, rfl, _, hw⟩ := hU_S01 e he
                      rcases hw with huw | hvw
                      · have heq : u = u0 := Finset.card_le_one.mp hW0_le1 u huw u0 hu0
                        subst heq
                        exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨v, Finset.mem_filter.mpr ⟨hv, he⟩, rfl⟩)
                      · have heq : v = v0 := Finset.card_le_one.mp hW1_le1 v hvw v0 hv0
                        subst heq
                        exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨u, Finset.mem_filter.mpr ⟨hu, he⟩, rfl⟩)
                    have hKX_U : (K ∪ {u0, v0}).card + (Ustar G D).card ≤ K.card + 3 + B_both.card := by
                      by_cases huv_in : s(u0, v0) ∈ Ustar G D
                      · have hv0_Nu0 : v0 ∈ Nu0 := Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hv0).2, huv_in⟩
                        have hu0_Nv0 : u0 ∈ Nv0 := Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hu0).2, huv_in⟩
                        have h_inter_ne : ((Nu0.image fun v => s(u0, v)) ∩
                            (Nv0.image fun u => s(u, v0))).Nonempty :=
                          ⟨s(u0, v0), Finset.mem_inter.mpr ⟨Finset.mem_image.mpr ⟨v0, hv0_Nu0, rfl⟩,
                            Finset.mem_image.mpr ⟨u0, hu0_Nv0, rfl⟩⟩⟩
                        have hU_le1 : (Ustar G D).card + 1 ≤ Nu0.card + Nv0.card := by
                          have h1 := Finset.card_le_card hU_sub_both
                          have h2 := Finset.card_union_add_card_inter (Nu0.image fun v => s(u0, v))
                            (Nv0.image fun u => s(u, v0))
                          have h3 := Finset.card_pos.mpr h_inter_ne
                          have h4 := Finset.card_image_le (f := fun v => s(u0, v)) (s := Nu0)
                          have h5 := Finset.card_image_le (f := fun u => s(u, v0)) (s := Nv0)
                          calc (Ustar G D).card + 1
                            _ ≤ (Nu0.image (fun v => s(u0, v)) ∪ Nv0.image (fun u => s(u, v0))).card +
                                (Nu0.image (fun v => s(u0, v)) ∩ Nv0.image (fun u => s(u, v0))).card :=
                              Nat.add_le_add h1 h3
                            _ = (Nu0.image (fun v => s(u0, v))).card + (Nv0.image (fun u => s(u, v0))).card := h2
                            _ ≤ Nu0.card + Nv0.card := Nat.add_le_add h4 h5
                        have hKU : (K ∪ {u0, v0}).card ≤ K.card + 2 := by
                          have h1 := Finset.card_union_le K ({u0, v0} : Finset (Fin N))
                          have h2 : ({u0, v0} : Finset (Fin N)).card ≤ 2 := Finset.card_le_two
                          omega
                        omega
                      · have hadj_uv : G.Adj u0 v0 := hW0_adj_S1 u0 hu0 v0 (Finset.mem_filter.mp hv0).2
                        have hH_uv : H.Adj u0 v0 := SimpleGraph.deleteEdges_adj.mpr ⟨hadj_uv, huv_in⟩
                        have hK_uv : u0 ∈ K ∨ v0 ∈ K := hK.1 hH_uv
                        have hKU : (K ∪ {u0, v0}).card ≤ K.card + 1 := by
                          rcases hK_uv with hu0K | hv0K
                          · have heq : K ∪ {u0, v0} = K ∪ {v0} := by
                              ext w; simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
                              constructor
                              · rintro (hw | rfl | rfl) <;> [exact Or.inl hw; exact Or.inl hu0K; exact Or.inr rfl]
                              · rintro (hw | rfl) <;> [exact Or.inl hw; exact Or.inr (Or.inr rfl)]
                            rw [heq]
                            exact le_trans (Finset.card_union_le K {v0}) (by rw [Finset.card_singleton])
                          · have heq : K ∪ {u0, v0} = K ∪ {u0} := by
                              ext w; simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
                              constructor
                              · rintro (hw | rfl | rfl) <;> [exact Or.inl hw; exact Or.inr rfl; exact Or.inl hv0K]
                              · rintro (hw | rfl) <;> [exact Or.inl hw; exact Or.inr (Or.inl rfl)]
                            rw [heq]
                            exact le_trans (Finset.card_union_le K {u0}) (by rw [Finset.card_singleton])
                        have hU_le2 : (Ustar G D).card ≤ Nu0.card + Nv0.card := by
                          have h1 := Finset.card_le_card hU_sub_both
                          have h2 := Finset.card_union_le (Nu0.image fun v => s(u0, v))
                            (Nv0.image fun u => s(u, v0))
                          have h3 := Finset.card_image_le (f := fun v => s(u0, v)) (s := Nu0)
                          have h4 := Finset.card_image_le (f := fun u => s(u, v0)) (s := Nv0)
                          calc (Ustar G D).card
                            _ ≤ (Nu0.image (fun v => s(u0, v)) ∪ Nv0.image (fun u => s(u, v0))).card := h1
                            _ ≤ (Nu0.image (fun v => s(u0, v))).card + (Nv0.image (fun u => s(u, v0))).card := h2
                            _ ≤ Nu0.card + Nv0.card := Nat.add_le_add h3 h4
                        omega
                    have hExtra2 : 2 ≤ 2 * (centreless G D).card + ((orN G D \ lam G D) \ B_both).card := by
                      by_cases hTc_empty : centreless G D = ∅
                      · dsimp only [W0'] at hu0'
                        dsimp only [W1'] at hv0'
                        rw [Finset.mem_filter] at hu0' hv0'
                        obtain ⟨v', hv'S1, hv'nW1, he_u⟩ := hu0'.2
                        obtain ⟨u', hu'S0, hu'nW0, he_v⟩ := hv0'.2
                        obtain ⟨au, hau, p1, q1, hpq1, _, bu, hreach_u, _, _, hside_u⟩ := hU_g s(u0, v') he_u
                        obtain ⟨av, hav, p2, q2, hpq2, _, bv, hreach_v, _, _, hside_v⟩ := hU_g s(u', v0) he_v
                        have hu0_side : u0 ∈ PEqualNP.TopForm.side D au (1 - bu) := by
                          rcases Sym2.eq_iff.mp hpq1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
                          · rcases hside_u with hp | hq
                            · exact hp
                            · have hw := hSide_wmax au hau bu hreach_u v' hq
                              exact False.elim (hv'nW1 (Finset.mem_filter.mpr ⟨hw, hv'S1⟩))
                          · rcases hside_u with hp | hq
                            · have hw := hSide_wmax au hau bu hreach_u v' hp
                              exact False.elim (hv'nW1 (Finset.mem_filter.mpr ⟨hw, hv'S1⟩))
                            · exact hq
                        have hv0_side : v0 ∈ PEqualNP.TopForm.side D av (1 - bv) := by
                          rcases Sym2.eq_iff.mp hpq2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
                          · rcases hside_v with hp | hq
                            · have hw := hSide_wmax av hav bv hreach_v u' hp
                              exact False.elim (hu'nW0 (Finset.mem_filter.mpr ⟨hw, hu'S0⟩))
                            · exact hq
                          · rcases hside_v with hp | hq
                            · exact hp
                            · have hw := hSide_wmax av hav bv hreach_v u' hq
                              exact False.elim (hu'nW0 (Finset.mem_filter.mpr ⟨hw, hu'S0⟩))
                        have hau_nc : au ∉ centreless G D := by rw [hTc_empty]; exact Finset.notMem_empty _
                        have hav_nc : av ∉ centreless G D := by rw [hTc_empty]; exact Finset.notMem_empty _
                        simp only [centreless, Finset.mem_filter, not_and, not_or] at hau_nc hav_nc
                        have hne_u : (PEqualNP.TopForm.side D au bu).Nonempty :=
                          Finset.nonempty_iff_ne_empty.mpr (by fin_cases bu; exact (hau_nc hau).1; exact (hau_nc hau).2)
                        have hne_v : (PEqualNP.TopForm.side D av bv).Nonempty :=
                          Finset.nonempty_iff_ne_empty.mpr (by fin_cases bv; exact (hav_nc hav).1; exact (hav_nc hav).2)
                        obtain ⟨hu_mix, hhu_mem, hgu, hreach_hu, hne_hu⟩ := hMix_reach (opnd D au bu) hne_u hreach_u
                        obtain ⟨hv_mix, hhv_mem, hgv, hreach_hv, _⟩ := hMix_reach (opnd D av bv) hne_v hreach_v
                        have hne_huv : hu_mix ≠ hv_mix := by
                          intro heq; subst heq
                          obtain ⟨z, hz⟩ := hne_hu
                          have hz_u : z ∈ PEqualNP.TopForm.side D au bu := hOrIn_mono _ _ z hreach_hu hz
                          have hz_v : z ∈ PEqualNP.TopForm.side D av bv := hOrIn_mono _ _ z hreach_hv hz
                          have hadj_zu : G.Adj z u0 := by
                            fin_cases bu
                            · exact (hTop_adj au hau z hz_u u0 hu0_side).1
                            · exact (hTop_adj au hau u0 hu0_side z hz_u).1.symm
                          have hadj_zv : G.Adj z v0 := by
                            fin_cases bv
                            · exact (hTop_adj av hav z hz_v v0 hv0_side).1
                            · exact (hTop_adj av hav v0 hv0_side z hz_v).1.symm
                          obtain ⟨col, hcol⟩ := hBip
                          have hadj_uv := hW0_adj_S1 u0 hu0 v0 (Finset.mem_filter.mp hv0).2
                          have h1 : col z ≠ col u0 := hcol hadj_zu
                          have h2 : col z ≠ col v0 := hcol hadj_zv
                          have h3 : col u0 ≠ col v0 := hcol hadj_uv
                          omega
                        have hnotB_u : hu_mix ∉ B_both := by
                          intro hb
                          have := hB_lt_g W_both (fun w hw => by
                            simp only [W_both, Finset.mem_insert, Finset.mem_singleton] at hw; exact hw) S_both hu_mix hb
                          omega
                        have hnotB_v : hv_mix ∉ B_both := by
                          intro hb
                          have := hB_lt_g W_both (fun w hw => by
                            simp only [W_both, Finset.mem_insert, Finset.mem_singleton] at hw; exact hw) S_both hv_mix hb
                          omega
                        have hsub2 : ({hu_mix, hv_mix} : Finset ℕ) ⊆ (orN G D \ lam G D) \ B_both := by
                          intro x hx
                          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
                          rcases hx with rfl | rfl
                          · exact Finset.mem_sdiff.mpr ⟨hhu_mem, hnotB_u⟩
                          · exact Finset.mem_sdiff.mpr ⟨hhv_mem, hnotB_v⟩
                        have hcard2 := Finset.card_le_card hsub2
                        rw [Finset.card_pair hne_huv] at hcard2
                        omega
                      · have hTc_ne : (centreless G D).Nonempty :=
                          Finset.nonempty_iff_ne_empty.mpr hTc_empty
                        have hpos : 1 ≤ (centreless G D).card := Finset.card_pos.mpr hTc_ne
                        exact le_trans (by omega : 2 ≤ 2 * (centreless G D).card) (Nat.le_add_right _ _)
                    have hB_both_sub : B_both ⊆ orN G D \ lam G D := Finset.filter_subset _ _
                    have hB_both_split := Finset.card_sdiff_add_card_eq_card hB_both_sub
                    refine ⟨K, {u0, v0}, hK, fun e he => ?_, ?_⟩
                    · rcases hU_cov2 e he with hu | hv
                      · exact ⟨u0, Finset.mem_union_right _ (by simp), hu⟩
                      · exact ⟨v0, Finset.mem_union_right _ (by simp), hv⟩
                    · omega
    · have hUempty : Ustar G D = ∅ := Finset.not_nonempty_iff_eq_empty.mp hU
      let H := G.deleteEdges ↑(Ustar G D)
      let coverSize (s : ℕ) := ∃ T : Finset (Fin (n + m)), H.IsVertexCover (↑T) ∧ T.card = s
      have univCover : H.IsVertexCover (↑(Finset.univ : Finset (Fin (n + m)))) := by
        intro a b _
        exact Or.inl (by simp)
      have existsCover : ∃ s, coverSize s := ⟨_, Finset.univ, univCover, rfl⟩
      obtain ⟨K, hKcovers, hKcard⟩ := Nat.find_spec existsCover
      have hK : IsMinCover H K := ⟨hKcovers, fun T hT =>
        hKcard ▸ Nat.find_min' existsCover (show coverSize T.card from ⟨T, hT, rfl⟩)⟩
      refine ⟨K, ∅, hK, ?_, ?_⟩
      · intro z hz
        rw [hUempty] at hz
        exact False.elim (Finset.notMem_empty z hz)
      · have hchargeK := (charge (n + m) G D hNo4 hEdges hDleast hDtop).2 K hK
        rw [Finset.union_empty, hUempty, Finset.card_empty, add_zero]
        omega
  obtain ⟨K, X, hK, hX, hb⟩ := hExtension
  have hcov (d : Fin n × Fin m) (hd : d ∈ E) : L d.1 ∈ K ∪ X ∨ R d.2 ∈ K ∪ X := by
    have hadj := (incidence d.1 d.2).mpr hd
    by_cases hmem : edge d ∈ Ustar G D
    · obtain ⟨v, hv, hve⟩ := hX (edge d) hmem
      rcases Sym2.mem_iff.mp hve with hh | hh
      · exact Or.inl (hh ▸ hv)
      · exact Or.inr (hh ▸ hv)
    · have hadj' : (G.deleteEdges ↑(Ustar G D)).Adj (L d.1) (R d.2) :=
        SimpleGraph.deleteEdges_adj.mpr ⟨hadj, hmem⟩
      rcases hK.1 hadj' with hv | hv
      · exact Or.inl (Finset.mem_union_left _ hv)
      · exact Or.inr (Finset.mem_union_left _ hv)
  have hbudget : E.card + (K ∪ X).card ≤ C.size + 1 := by
    rw [hcard, hDsize] at hc
    omega
  obtain ⟨F, hF, hFsize, hFval⟩ := compileStars n m (E.erase e) (K ∪ X)
    (fun d hd => hcov d (Finset.mem_of_mem_erase hd))
  refine ⟨e, he, heM, F, ?_, hF, hFval⟩
  rw [Finset.card_erase_of_mem he] at hFsize
  have hEpos : 0 < E.card := Finset.card_pos.mpr ⟨e, he⟩
  have hTpos : 0 < (K ∪ X).card := Finset.card_pos.mpr <|
    (hcov e he).elim (fun h => ⟨_, h⟩) (fun h => ⟨_, h⟩)
  omega
