import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.R_meta_2583_1

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.ReadK PEqualNP.ReadTwo PEqualNP.Core
open PEqualNP.CircuitMoves


open Classical

private def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

private lemma foldl_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

private lemma foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

private lemma getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

private lemma wval_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : ℕ) (hi : i < n) :
    wval C x i = x ⟨i, hi⟩ := by
  unfold wval
  rw [wires_eq_foldl, foldl_getD_lt]
  · simp [List.getD_eq_getElem?_getD, hi]
  · simp [hi]

private lemma wval_gate_ge {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hw : n + C.gates.length ≤ w) : wval C x w = false := by
  unfold wval
  rw [wires_eq_foldl]
  apply getD_ge
  rw [foldl_length, List.length_ofFn]
  exact hw

private lemma wval_gate_eval {n : ℕ} (C : Circuit) (x : Fin n → Bool) (j : ℕ)
    (hj : j < C.gates.length) :
    wval C x (n + j) =
      (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
        if i < n + j then wval C x i else false) := by
  unfold wval gateAt
  rw [wires_eq_foldl]
  have hlen : (List.ofFn x).length = n := List.length_ofFn
  have hstep : ∀ (gs : List Gate) (w : List Bool) (k : ℕ) (hk : k < gs.length),
      (gs.foldl stepWire w).getD (w.length + k) false =
        (gs[k]).op.eval ((gs[k]).inputs.map fun i =>
          if i < w.length + k then (gs.foldl stepWire w).getD i false else false) := by
    intro gs w k hk
    induction gs generalizing w k with
    | nil => simp at hk
    | cons g gs ih =>
      rw [List.foldl_cons]
      cases k with
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
      | succ k =>
        have hk' : k < gs.length := by simp at hk; omega
        have ihk := ih (stepWire w g) k hk'
        have hlen1 : (stepWire w g).length = w.length + 1 := by simp [stepWire]
        rw [hlen1] at ihk
        have heq : w.length + 1 + k = w.length + (k + 1) := by omega
        rw [heq] at ihk
        simpa [List.getElem_cons_succ] using ihk
  have hres := hstep C.gates (List.ofFn x) j hj
  rw [hlen] at hres
  simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj] using hres

private lemma wval_gate_eval_rb {n : ℕ} (C : Circuit) (hrb : ReadsBack n C)
    (x : Fin n → Bool) (j : ℕ) (hj : j < C.gates.length) :
    wval C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map (wval C x)) := by
  rw [wval_gate_eval C x j hj]
  congr 1
  apply List.map_congr_left
  intro i hi
  rw [if_pos (hrb j hj i hi)]

private lemma gateOp_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    {l₁ l₂ : List Bool} (hlen : l₁.length = l₂.length)
    (hle : ∀ i (hi : i < l₁.length), l₁[i] = true → l₂[i]'(hlen ▸ hi) = true) :
    op.eval l₁ = true → op.eval l₂ = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_eq_true, id_eq]
    intro h a ha
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
    have := h _ (List.getElem_mem (hlen ▸ hi))
    exact hle i (hlen ▸ hi) this
  · simp only [GateOp.eval, List.any_eq_true, id_eq]
    rintro ⟨a, ha, htrue⟩
    obtain ⟨i, hi, hia⟩ := List.getElem_of_mem ha
    exact ⟨l₂[i]'(hlen ▸ hi), List.getElem_mem _, hle i hi (hia.trans htrue)⟩

private lemma foldl_stepWire_append (gs₁ gs₂ : List Gate) (w : List Bool) :
    (gs₁ ++ gs₂).foldl stepWire w = gs₂.foldl stepWire (gs₁.foldl stepWire w) :=
  List.foldl_append

private lemma wval_append_lt {n : ℕ} (gs₁ gs₂ : List Gate) (out : ℕ) (x : Fin n → Bool)
    (w : ℕ) (hw : w < n + gs₁.length) :
    wval ⟨gs₁ ++ gs₂, out⟩ x w = wval ⟨gs₁, out⟩ x w := by
  unfold wval
  rw [wires_eq_foldl, wires_eq_foldl, foldl_stepWire_append, foldl_getD_lt]
  rw [foldl_length, List.length_ofFn]
  exact hw

private lemma output_lt_of_eval_true {n : ℕ} (C : Circuit) (x : Fin n → Bool)
    (htrue : circuitFun n C x = true) : C.output < n + C.gates.length := by
  by_contra hge
  push Not at hge
  have h0 : circuitFun n C x = wval C x C.output := rfl
  rw [h0, wval_gate_ge C x C.output hge] at htrue
  cases htrue

private lemma wval_eraseGate_lt {n : ℕ} (C : Circuit) (m p : ℕ) (hm : m < C.gates.length)
    (x : Fin n → Bool) (w : ℕ) (hw : w < n + m) :
    wval (eraseGate n C m p) x w = wval C x w := by
  unfold eraseGate
  rw [if_pos hm]
  have h1 : wval ⟨C.gates.take m ++ (C.gates.drop (m + 1)).map
      (fun g => ⟨g.op, g.inputs.map (eraseRedirect n m p)⟩), eraseRedirect n m p C.output⟩ x w =
      wval ⟨C.gates.take m, eraseRedirect n m p C.output⟩ x w := by
    apply wval_append_lt
    simp [List.length_take, Nat.min_eq_left hm.le]
    exact hw
  have h2 : C.gates = C.gates.take m ++ C.gates.drop m := (List.take_append_drop m C.gates).symm
  have h3 : wval C x w = wval ⟨C.gates.take m, C.output⟩ x w := by
    have hEq : wval C x w = wval ⟨C.gates.take m ++ C.gates.drop m, C.output⟩ x w := by
      unfold wval; rw [← h2]
    rw [hEq]
    apply wval_append_lt
    simp [List.length_take, Nat.min_eq_left hm.le]
    exact hw
  rw [h1, h3]
  rfl

private lemma gateAt_eraseGate_lt {n : ℕ} (C : Circuit) (m p j : ℕ) (hm : m < C.gates.length)
    (hj : j < m) : gateAt (eraseGate n C m p) j = gateAt C j := by
  unfold eraseGate gateAt
  rw [if_pos hm]
  simp only [List.getD_eq_getElem?_getD]
  have hlen : (C.gates.take m).length = m := List.length_take_of_le hm.le
  rw [List.getElem?_append_left (by omega), List.getElem?_take_of_lt hj,
    List.getElem?_eq_getElem (by omega)]

private lemma gateAt_eraseGate_ge {n : ℕ} (C : Circuit) (m p j : ℕ) (hm : m < C.gates.length)
    (hjm : m ≤ j) (hj : j + 1 < C.gates.length) :
    gateAt (eraseGate n C m p) j =
      ⟨(gateAt C (j + 1)).op, (gateAt C (j + 1)).inputs.map (eraseRedirect n m p)⟩ := by
  unfold eraseGate gateAt
  rw [if_pos hm]
  simp only [List.getD_eq_getElem?_getD]
  have hlen : (C.gates.take m).length = m := List.length_take_of_le hm.le
  rw [List.getElem?_append_right (by omega), hlen]
  have hidx : j - m < (C.gates.drop (m + 1)).length := by simp; omega
  rw [List.getElem?_map, List.getElem?_drop, List.getElem?_eq_getElem (by omega),
    List.getElem?_eq_getElem hj]
  have : m + 1 + (j - m) = j + 1 := by omega
  simp [this]

private lemma eraseGate_length {n : ℕ} (C : Circuit) (m p : ℕ) (hm : m < C.gates.length) :
    (eraseGate n C m p).gates.length = C.gates.length - 1 := by
  unfold eraseGate
  rw [if_pos hm]
  simp [List.length_take, List.length_drop, hm.le]
  omega

private lemma eraseGate_isAO2 {n : ℕ} (C : Circuit) (m p : ℕ) (hAO : IsAO2 n C)
    (hm : m < C.gates.length) (hp : p < n + m) :
    IsAO2 n (eraseGate n C m p) := by
  rcases hAO with ⟨hAndOr, hrb, hlen2⟩
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    unfold eraseGate at hg
    rw [if_pos hm] at hg
    simp only [List.mem_append, List.mem_map] at hg
    rcases hg with hg | ⟨g', hg', rfl⟩
    · exact hAndOr g (List.mem_of_mem_take hg)
    · exact hAndOr g' (List.mem_of_mem_drop hg')
  · intro j hj i hi
    rw [eraseGate_length C m p hm] at hj
    by_cases hjm : j < m
    · rw [gateAt_eraseGate_lt C m p j hm hjm] at hi
      exact hrb j (by omega) i hi
    · have hjm' : m ≤ j := by omega
      rw [gateAt_eraseGate_ge C m p j hm hjm' (by omega)] at hi
      simp only [List.mem_map] at hi
      rcases hi with ⟨k, hk, rfl⟩
      have hklt : k < n + (j + 1) := hrb (j + 1) (by omega) k hk
      unfold eraseRedirect
      split_ifs with h1 h2
      · omega
      · omega
      · omega
  · intro g hg
    unfold eraseGate at hg
    rw [if_pos hm] at hg
    simp only [List.mem_append, List.mem_map] at hg
    rcases hg with hg | ⟨g', hg', rfl⟩
    · exact hlen2 g (List.mem_of_mem_take hg)
    · simp [hlen2 g' (List.mem_of_mem_drop hg')]

private lemma eraseRedirect_lt_of_lt {n m p i bound : ℕ} (hm : m < bound) (hp : p < n + m)
    (hi : i < n + bound) : eraseRedirect n m p i < n + (bound - 1) := by
  unfold eraseRedirect
  split_ifs <;> omega

private lemma liftAt_isAO2 {n : ℕ} (C : Circuit) (m p h : ℕ) (hAO : IsAO2 n C)
    (hm : m < C.gates.length) (hp : p < n + m) (hh : h < n + m)
    (hout : C.output < n + C.gates.length) :
    IsAO2 n (liftAt n C m p h) := by
  have hE := eraseGate_isAO2 C m p hAO hm hp
  have hElen := eraseGate_length (n := n) C m p hm
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    unfold liftAt at hg
    simp only [List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | rfl
    · exact hE.1 g hg
    · exact Or.inr rfl
  · intro j hj i hi
    have hj' : j < (eraseGate n C m p).gates.length + 1 := by simpa [liftAt] using hj
    by_cases hjlt : j < (eraseGate n C m p).gates.length
    · have hgat : gateAt (liftAt n C m p h) j = gateAt (eraseGate n C m p) j := by
        unfold liftAt gateAt
        simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hjlt]
      rw [hgat] at hi
      exact hE.2.1 j hjlt i hi
    · have hjeq : j = (eraseGate n C m p).gates.length := by omega
      subst hjeq
      have hgat : gateAt (liftAt n C m p h) (eraseGate n C m p).gates.length =
          ⟨GateOp.or, [(eraseGate n C m p).output, h]⟩ := by
        unfold liftAt gateAt
        simp [List.getD_eq_getElem?_getD]
      rw [hgat] at hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      · rw [hElen]
        unfold eraseGate
        rw [if_pos hm]
        exact eraseRedirect_lt_of_lt hm hp hout
      · omega
  · intro g hg
    unfold liftAt at hg
    simp only [List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | rfl
    · exact hE.2.2 g hg
    · rfl

private lemma liftAt_size {n : ℕ} (C : Circuit) (m p h : ℕ) (hm : m < C.gates.length) :
    (liftAt n C m p h).size = C.size := by
  unfold liftAt Circuit.size
  simp [eraseGate_length C m p hm]
  omega

private lemma wval_eraseGate_le {n : ℕ} (C : Circuit) (hAO : IsAO2 n C)
    (m p h : ℕ) (hm : m < C.gates.length) (hp : p < n + m)
    (hm_or : (gateAt C m).op = GateOp.or)
    (hm_in : (gateAt C m).inputs = [p, h] ∨ (gateAt C m).inputs = [h, p])
    (x : Fin n → Bool) :
    (∀ j < C.gates.length, j ≠ m →
      wval (eraseGate n C m p) x (n + (if j < m then j else j - 1)) = true →
      wval C x (n + j) = true) ∧
    (wval C x h = false → ∀ j < C.gates.length, j ≠ m →
      wval (eraseGate n C m p) x (n + (if j < m then j else j - 1)) = wval C x (n + j)) := by
  have hE := eraseGate_isAO2 C m p hAO hm hp
  have hElen := eraseGate_length (n := n) C m p hm
  have hm_eval : wval C x (n + m) = (wval C x p || wval C x h) := by
    rw [wval_gate_eval_rb C hAO.2.1 x m hm, hm_or]
    rcases hm_in with hin | hin <;> simp [hin, GateOp.eval, Bool.or_comm]
  have hstep : ∀ k : ℕ, k < C.gates.length → k ≠ m →
      (wval (eraseGate n C m p) x (n + (if k < m then k else k - 1)) = true →
        wval C x (n + k) = true) ∧
      (wval C x h = false →
        wval (eraseGate n C m p) x (n + (if k < m then k else k - 1)) = wval C x (n + k)) := by
    intro k
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      intro hk hne
      by_cases hkm : k < m
      · rw [if_pos hkm]
        have heq : wval (eraseGate n C m p) x (n + k) = wval C x (n + k) :=
          wval_eraseGate_lt C m p hm x (n + k) (by omega)
        rw [heq]
        exact ⟨id, fun _ => rfl⟩
      · have hmk : m < k := by omega
        rw [if_neg hkm]
        have hk1 : k - 1 < (eraseGate n C m p).gates.length := by omega
        have heq1 : (k - 1) + 1 = k := by omega
        have hwireE := wval_gate_eval_rb (eraseGate n C m p) hE.2.1 x (k - 1) hk1
        have hwireC := wval_gate_eval_rb C hAO.2.1 x k hk
        rw [gateAt_eraseGate_ge C m p (k - 1) hm (by omega) (by omega), heq1] at hwireE
        have hop : (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or := by
          apply hAO.1
          unfold gateAt
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
          exact List.getElem_mem hk
        constructor
        · intro htrue
          rw [hwireE, List.map_map] at htrue
          rw [hwireC]
          apply gateOp_mono (gateAt C k).op hop (by simp) _ htrue
          intro i hi hval
          simp only [List.length_map] at hi
          simp only [List.getElem_map, Function.comp_apply] at hval ⊢
          set w := (gateAt C k).inputs[i]
          have hwlt : w < n + k := hAO.2.1 k hk w (List.getElem_mem hi)
          unfold eraseRedirect at hval
          split_ifs at hval with hw1 hw2
          · rw [hw1, hm_eval, Bool.or_eq_true]
            left
            rwa [← wval_eraseGate_lt C m p hm x p hp]
          · have hsub : w - n < k ∧ w - n ≠ m := ⟨by omega, by omega⟩
            have hi_sub := (ih (w - n) hsub.1 (by omega) hsub.2).1
            have hidx : (if w - n < m then w - n else w - n - 1) = w - n - 1 := by
              simp [show ¬ w - n < m by omega]
            have hw_eq : n + (w - n - 1) = w - 1 := by omega
            have hw_eq2 : n + (w - n) = w := by omega
            rw [hidx, hw_eq] at hi_sub
            rw [hw_eq2] at hi_sub
            exact hi_sub hval
          · rwa [← wval_eraseGate_lt C m p hm x w (by omega)]
        · intro hhfalse
          rw [hwireE, hwireC, List.map_map]
          congr 1
          apply List.map_congr_left
          intro w hw
          have hwlt : w < n + k := hAO.2.1 k hk w hw
          simp only [Function.comp_apply]
          unfold eraseRedirect
          split_ifs with hw1 hw2
          · rw [hw1, hm_eval, hhfalse, Bool.or_false, wval_eraseGate_lt C m p hm x p hp]
          · have hi_sub := (ih (w - n) (by omega) (by omega) (by omega)).2 hhfalse
            have hidx : (if w - n < m then w - n else w - n - 1) = w - n - 1 := by
              simp [show ¬ w - n < m by omega]
            have hw_eq : n + (w - n - 1) = w - 1 := by omega
            have hw_eq2 : n + (w - n) = w := by omega
            rw [hidx, hw_eq, hw_eq2] at hi_sub
            exact hi_sub
          · exact wval_eraseGate_lt C m p hm x w (by omega)
  exact ⟨fun j hj hne => (hstep j hj hne).1, fun hh j hj hne => (hstep j hj hne).2 hh⟩

private lemma liftAt_eval {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hfun : circuitFun n C = graphFun G ∅)
    (m p h : ℕ) (hm : m < C.gates.length) (hp : p < n + m) (hh : h < n + m)
    (hm_or : (gateAt C m).op = GateOp.or)
    (hm_in : (gateAt C m).inputs = [p, h] ∨ (gateAt C m).inputs = [h, p])
    (himp : IsImpWire G C h) (hout : C.output < n + C.gates.length) :
    circuitFun n (liftAt n C m p h) = graphFun G ∅ := by
  funext x
  have hL_AO := liftAt_isAO2 C m p h hAO hm hp hh hout
  have hElen := eraseGate_length (n := n) C m p hm
  have hEout : (eraseGate n C m p).output < n + (eraseGate n C m p).gates.length := by
    rw [hElen]
    unfold eraseGate
    rw [if_pos hm]
    exact eraseRedirect_lt_of_lt hm hp hout
  have hcf : circuitFun n (liftAt n C m p h) x =
      wval (liftAt n C m p h) x (n + (eraseGate n C m p).gates.length) := rfl
  rw [hcf, wval_gate_eval_rb (liftAt n C m p h) hL_AO.2.1 x (eraseGate n C m p).gates.length
    (by simp [liftAt])]
  have hgat : gateAt (liftAt n C m p h) (eraseGate n C m p).gates.length =
      ⟨GateOp.or, [(eraseGate n C m p).output, h]⟩ := by
    unfold liftAt gateAt
    simp [List.getD_eq_getElem?_getD]
  rw [hgat]
  simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, Bool.or_false, id_eq]
  have hw1 : wval (liftAt n C m p h) x (eraseGate n C m p).output =
      wval (eraseGate n C m p) x (eraseGate n C m p).output :=
    wval_append_lt (eraseGate n C m p).gates [⟨GateOp.or, [(eraseGate n C m p).output, h]⟩]
      (eraseGate n C m p).output x (eraseGate n C m p).output hEout
  have hw2 : wval (liftAt n C m p h) x h = wval (eraseGate n C m p) x h :=
    wval_append_lt (eraseGate n C m p).gates [⟨GateOp.or, [(eraseGate n C m p).output, h]⟩]
      (eraseGate n C m p).output x h (by omega)
  rw [hw1, hw2, wval_eraseGate_lt C m p hm x h hh]
  by_cases hhx : wval C x h = true
  · rw [hhx, Bool.or_true]
    exact (himp.1 x hhx).symm
  · have hhf : wval C x h = false := Bool.eq_false_iff.mpr hhx
    rw [hhf, Bool.or_false]
    have hle := (wval_eraseGate_le C hAO m p h hm hp hm_or hm_in x).2 hhf
    have hEout_eq : wval (eraseGate n C m p) x (eraseGate n C m p).output = wval C x C.output := by
      have hout_eq : (eraseGate n C m p).output = eraseRedirect n m p C.output := by
        unfold eraseGate; rw [if_pos hm]
      rw [hout_eq]
      unfold eraseRedirect
      split_ifs with h1 h2
      · rw [h1]
        have hm_eval : wval C x (n + m) = (wval C x p || wval C x h) := by
          rw [wval_gate_eval_rb C hAO.2.1 x m hm, hm_or]
          rcases hm_in with hin | hin <;> simp [hin, GateOp.eval, Bool.or_comm]
        rw [hm_eval, hhf, Bool.or_false, wval_eraseGate_lt C m p hm x p hp]
      · have hj : C.output - n < C.gates.length ∧ C.output - n ≠ m ∧ ¬ C.output - n < m := by omega
        have hstep := hle (C.output - n) hj.1 hj.2.1
        rw [if_neg hj.2.2] at hstep
        have heq1 : n + (C.output - n - 1) = C.output - 1 := by omega
        have heq2 : n + (C.output - n) = C.output := by omega
        rw [heq1, heq2] at hstep
        exact hstep
      · exact wval_eraseGate_lt C m p hm x C.output (by omega)
    rw [hEout_eq]
    exact congrFun hfun x

private lemma orN_liftAt_lt {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hfun : circuitFun n C = graphFun G ∅)
    (m p h : ℕ) (hm : m < C.gates.length) (hp : p < n + m) (hh : h < n + m)
    (hm_or : (gateAt C m).op = GateOp.or)
    (hm_not_below : ¬ BelowF G C m)
    (hm_in : (gateAt C m).inputs = [p, h] ∨ (gateAt C m).inputs = [h, p])
    (himp : IsImpWire G C h) (hout : C.output < n + C.gates.length) :
    (orN G (liftAt n C m p h)).card < (orN G C).card := by
  set C' := liftAt n C m p h
  have hC'fun := liftAt_eval G C hAO hfun m p h hm hp hh hm_or hm_in himp hout
  have hElen := eraseGate_length (n := n) C m p hm
  have hm_mem : m ∈ orN G C := by
    simp only [orN, gatesWhere, Finset.mem_filter, Finset.mem_range]
    exact ⟨hm, hm_or, hm_not_below⟩
  let f : ℕ → ℕ := fun j => if j < m then j else j + 1
  have hinj : ∀ j₁ ∈ orN G C', ∀ j₂ ∈ orN G C', f j₁ = f j₂ → j₁ = j₂ := by
    intro j₁ _ j₂ _ hf
    dsimp only [f] at hf
    split_ifs at hf <;> omega
  have hmaps : ∀ j ∈ orN G C', f j ∈ (orN G C).erase m := by
    intro j hj
    simp only [orN, gatesWhere, Finset.mem_filter, Finset.mem_range] at hj
    rcases hj with ⟨hjlen, hjor, hjnb⟩
    have hjlt : j < (eraseGate n C m p).gates.length := by
      have hlen' : C'.gates.length = (eraseGate n C m p).gates.length + 1 := by
        simp [C', liftAt]
      by_contra hge
      push Not at hge
      have hjeq : j = (eraseGate n C m p).gates.length := by omega
      apply hjnb
      intro x hx
      have hcf : wval C' x (n + j) = circuitFun n C' x := by
        rw [hjeq]; rfl
      change wval C' x (n + j) = true at hx
      rw [hcf, hC'fun] at hx
      exact hx
    dsimp only [f]
    rw [Finset.mem_erase]
    refine ⟨by split_ifs <;> omega, ?_⟩
    simp only [orN, gatesWhere, Finset.mem_filter, Finset.mem_range]
    have hgat : gateAt C' j = gateAt (eraseGate n C m p) j := by
      unfold gateAt C' liftAt
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hjlt]
    refine ⟨by split_ifs <;> omega, ?_, ?_⟩
    · split_ifs with hjm
      · rwa [hgat, gateAt_eraseGate_lt C m p j hm hjm] at hjor
      · rw [hgat, gateAt_eraseGate_ge C m p j hm (by omega) (by omega)] at hjor
        exact hjor
    · intro hbelow
      apply hjnb
      intro x hx
      apply hbelow x
      have hx' : wval C' x (n + j) = true := hx
      have hwe : wval C' x (n + j) = wval (eraseGate n C m p) x (n + j) :=
        wval_append_lt _ _ _ x (n + j) (by omega)
      rw [hwe] at hx'
      split_ifs with hjm
      · rwa [wval_eraseGate_lt C m p hm x (n + j) (by omega)] at hx'
      · have hle := (wval_eraseGate_le C hAO m p h hm hp hm_or hm_in x).1 (j + 1) (by omega) (by omega)
        rw [if_neg (by omega)] at hle
        exact hle hx'
  have hle : (orN G C').card ≤ ((orN G C).erase m).card :=
    Finset.card_le_card_of_injOn f hmaps (fun j₁ h₁ j₂ h₂ => hinj j₁ h₁ j₂ h₂)
  have hlt : ((orN G C).erase m).card < (orN G C).card :=
    Finset.card_erase_lt_of_mem hm_mem
  omega

lemma lift_normalize {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hne : G.edgeFinset.Nonempty) (C : Circuit) (hAO : IsAO2 n C)
    (hfun : circuitFun n C = graphFun G ∅) :
    ∃ C' : Circuit, IsAO2 n C' ∧ circuitFun n C' = graphFun G ∅ ∧
      C'.size ≤ C.size ∧ IsLiftFixedPoint G C' := by
  suffices h : ∀ k : ℕ, ∀ C : Circuit, (orN G C).card = k → IsAO2 n C →
      circuitFun n C = graphFun G ∅ →
      ∃ C' : Circuit, IsAO2 n C' ∧ circuitFun n C' = graphFun G ∅ ∧
        C'.size ≤ C.size ∧ IsLiftFixedPoint G C' by
    exact h (orN G C).card C rfl hAO hfun
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro C hk hAO hfun
    by_cases hfp : IsLiftFixedPoint G C
    · exact ⟨C, hAO, hfun, le_refl _, hfp⟩
    · unfold IsLiftFixedPoint LiftApplies at hfp
      push Not at hfp
      obtain ⟨m, hm, b, hLift⟩ := hfp
      rcases hLift with ⟨_, hm_or, hm_not_below, himp⟩
      set p := opnd C m (1 - b)
      set h := opnd C m b
      have hlen2 : (gateAt C m).inputs.length = 2 := by
        apply hAO.2.2
        unfold gateAt
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hm]
        exact List.getElem_mem hm
      have hp_mem : p ∈ (gateAt C m).inputs := by
        fin_cases b <;> simp [p, opnd, List.getD_eq_getElem?_getD] <;>
          rw [List.getElem?_eq_getElem (by omega)] <;> exact List.getElem_mem _
      have hh_mem : h ∈ (gateAt C m).inputs := by
        fin_cases b <;> simp [h, opnd, List.getD_eq_getElem?_getD] <;>
          rw [List.getElem?_eq_getElem (by omega)] <;> exact List.getElem_mem _
      have hp : p < n + m := hAO.2.1 m hm p hp_mem
      have hh : h < n + m := hAO.2.1 m hm h hh_mem
      have hm_in : (gateAt C m).inputs = [p, h] ∨ (gateAt C m).inputs = [h, p] := by
        match hin : (gateAt C m).inputs with
        | [] => simp [hin] at hlen2
        | [_] => simp [hin] at hlen2
        | [a₀, a₁] =>
          fin_cases b
          · right; simp [p, h, opnd, hin]
          · left; simp [p, h, opnd, hin]
        | _ :: _ :: _ :: _ => simp [hin] at hlen2
      have hout : C.output < n + C.gates.length := by
        obtain ⟨e, he⟩ := hne
        induction e using Sym2.ind with
        | _ u v =>
          have huv : G.Adj u v := SimpleGraph.mem_edgeFinset.mp he
          have htrue : circuitFun n C (pairInput u v) = true := by
            rw [hfun]
            simp [graphFun, pairInput]
            exact ⟨u, v, huv, Or.inl rfl, Or.inr rfl⟩
          exact output_lt_of_eval_true C (pairInput u v) htrue
      set C₁ := liftAt n C m p h
      have hAO₁ := liftAt_isAO2 C m p h hAO hm hp hh hout
      have hfun₁ := liftAt_eval G C hAO hfun m p h hm hp hh hm_or hm_in himp hout
      have hcard₁ := orN_liftAt_lt G C hAO hfun m p h hm hp hh hm_or hm_not_below hm_in himp hout
      rw [hk] at hcard₁
      obtain ⟨C', hAO', hfun', hsize', hfp'⟩ := ih (orN G C₁).card hcard₁ C₁ rfl hAO₁ hfun₁
      exact ⟨C', hAO', hfun', hsize'.trans (liftAt_size C m p h hm).le, hfp'⟩

/-! Lemma 2: From lift-fixed-point + least + core-free to Read-1 -/

def incGraph (N : ℕ) (I : Fin N → Fin N → Prop) : SimpleGraph (Fin (N + N)) where
  Adj u v :=
    (∃ p l : Fin N, I p l ∧ u = Fin.castAdd N p ∧ v = Fin.natAdd N l) ∨
    (∃ p l : Fin N, I p l ∧ u = Fin.natAdd N l ∧ v = Fin.castAdd N p)
  symm := ⟨fun _ _ h => by
    rcases h with ⟨p, l, hI, rfl, rfl⟩ | ⟨p, l, hI, rfl, rfl⟩
    · exact Or.inr ⟨p, l, hI, rfl, rfl⟩
    · exact Or.inl ⟨p, l, hI, rfl, rfl⟩⟩
  loopless := ⟨fun _ h => by
    rcases h with ⟨p, l, _, h1, h2⟩ | ⟨p, l, _, h1, h2⟩
    · have := congrArg Fin.val (h1.symm.trans h2)
      simp only [Fin.coe_castAdd, Fin.coe_natAdd] at this
      omega
    · have := congrArg Fin.val (h1.symm.trans h2)
      simp only [Fin.coe_castAdd, Fin.coe_natAdd] at this
      omega⟩

private lemma graphFun_incGraph {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (z : Fin (N + N) → Bool) :
    graphFun (incGraph N I) ∅ z =
      decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) := by
  simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or]
  apply decide_eq_decide.mpr
  constructor
  · rintro ⟨u, v, huv, hu, hv⟩
    rcases huv with ⟨p, l, hI, rfl, rfl⟩ | ⟨p, l, hI, rfl, rfl⟩
    · exact ⟨p, l, hI, hu, hv⟩
    · exact ⟨p, l, hI, hv, hu⟩
  · rintro ⟨p, l, hI, hp, hl⟩
    exact ⟨Fin.castAdd N p, Fin.natAdd N l, Or.inl ⟨p, l, hI, rfl, rfl⟩, hp, hl⟩

private lemma exists_leastAO {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hne : G.edgeFinset.Nonempty) (C : Circuit) (hAO : IsAO2 n C)
    (hfun : circuitFun n C = graphFun G ∅) :
    ∃ C' : Circuit, IsLeastAO G C' ∧ C'.size ≤ C.size ∧ IsLiftFixedPoint G C' := by
  have hex : ∃ k : ℕ, ∃ C₀ : Circuit, IsAO2 n C₀ ∧ circuitFun n C₀ = graphFun G ∅ ∧ C₀.size = k :=
    ⟨C.size, C, hAO, hfun, rfl⟩
  let k := Nat.find hex
  obtain ⟨C₀, hAO₀, hfun₀, hk₀⟩ := Nat.find_spec hex
  have hle : C₀.size ≤ C.size := hk₀ ▸ Nat.find_min' hex ⟨C, hAO, hfun, rfl⟩
  obtain ⟨C', hAO', hfun', hsz', hfp'⟩ := lift_normalize G hne C₀ hAO₀ hfun₀
  refine ⟨C', ⟨hAO', hfun', ?_⟩, hsz'.trans hle, hfp'⟩
  intro D hDAO hDfun
  have hDge : k ≤ D.size := Nat.find_min' hex ⟨D, hDAO, hDfun, rfl⟩
  have hC'eq : C'.size = k :=
    le_antisymm (by dsimp only [k]; rw [← hk₀]; exact hsz') (Nat.find_min' hex ⟨C', hAO', hfun', rfl⟩)
  omega

private lemma prime_implicant_of_incGraph {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (D : Circuit) (hfun : circuitFun (N + N) D = graphFun (incGraph N I) ∅)
    (S : Finset (Fin (N + N))) (hS : IsPrimeImplicant (N + N) D S) :
    ∃ p l : Fin N, I p l ∧ S = {Fin.castAdd N p, Fin.natAdd N l} := by
  have h1 : graphFun (incGraph N I) ∅ (setInput S) = true := by
    rw [← hfun]; exact hS.1
  rw [graphFun_incGraph] at h1
  simp only [decide_eq_true_eq, setInput] at h1
  obtain ⟨p, l, hI, hp, hl⟩ := h1
  refine ⟨p, l, hI, ?_⟩
  let T : Finset (Fin (N + N)) := {Fin.castAdd N p, Fin.natAdd N l}
  have hTsub : T ⊆ S := by
    intro x hx
    simp only [T, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
  by_contra hne
  have hTss : T ∈ S.ssubsets :=
    Finset.mem_ssubsets.mpr ⟨hTsub, fun h => hne (Finset.Subset.antisymm hTsub h).symm⟩
  have hTfalse := hS.2 T hTss
  have hTtrue : circuitFun (N + N) D (setInput T) = true := by
    rw [hfun, graphFun_incGraph]
    simp only [decide_eq_true_eq, setInput]
    exact ⟨p, l, hI, by simp [T], by simp [T]⟩
  rw [hTtrue] at hTfalse
  cases hTfalse

private lemma readVectors_output_irrel (C : Circuit) (n : ℕ) (S : List ℕ) (k : ℕ) (out : ℕ) :
    readVectors { C with output := out } n S k = readVectors C n S k := rfl

private lemma mem_insertNew {A : List (List ℕ)} {v u : List ℕ} (hu : u ∈ A) :
    u ∈ insertNew A v := by
  unfold insertNew
  split_ifs
  · exact hu
  · exact List.mem_append_left _ hu

private lemma mem_insertNew_self (A : List (List ℕ)) (v : List ℕ) :
    v ∈ insertNew A v := by
  unfold insertNew
  split_ifs with h
  · exact h
  · exact List.mem_append_right _ (List.mem_singleton_self _)

private lemma mem_foldl_insertNew_acc (A acc : List (List ℕ)) (u : List ℕ) (hu : u ∈ acc) :
    u ∈ A.foldl insertNew acc := by
  induction A generalizing acc with
  | nil => exact hu
  | cons v A ih => exact ih _ (mem_insertNew hu)

private lemma mem_foldl_insertNew_mem (A acc : List (List ℕ)) (u : List ℕ) (hu : u ∈ A) :
    u ∈ A.foldl insertNew acc := by
  induction A generalizing acc with
  | nil => simp at hu
  | cons v A ih =>
    simp only [List.mem_cons] at hu
    rcases hu with rfl | hu
    · exact mem_foldl_insertNew_acc A _ u (mem_insertNew_self acc u)
    · exact ih _ hu

private lemma mem_foldl_or_acc (ins : List (List (List ℕ))) (acc : List (List ℕ)) (u : List ℕ)
    (hu : u ∈ acc) : u ∈ ins.foldl (fun acc A => A.foldl insertNew acc) acc := by
  induction ins generalizing acc with
  | nil => exact hu
  | cons A ins ih => exact ih _ (mem_foldl_insertNew_acc A acc u hu)

private lemma mem_foldl_or_mem (ins : List (List (List ℕ))) (acc : List (List ℕ)) (A : List (List ℕ))
    (hA : A ∈ ins) (u : List ℕ) (hu : u ∈ A) :
    u ∈ ins.foldl (fun acc A => A.foldl insertNew acc) acc := by
  induction ins generalizing acc with
  | nil => simp at hA
  | cons B ins ih =>
    simp only [List.mem_cons] at hA
    rcases hA with rfl | hA
    · exact mem_foldl_or_acc ins _ u (mem_foldl_insertNew_mem A acc u hu)
    · exact ih _ hA

private lemma readVectors_or_subset (C : Circuit) (n : ℕ) (S : List ℕ) (k : ℕ)
    (hrb : ReadsBack n C) (j : ℕ) (hj : j < C.gates.length)
    (hjor : (gateAt C j).op = GateOp.or) (w : ℕ) (hw : w ∈ (gateAt C j).inputs)
    (v : List ℕ) (hv : v ∈ (readVectors C n S k).getD w []) :
    v ∈ (readVectors C n S k).getD (n + j) [] := by
  let rvStep : List (List (List ℕ)) → Gate → List (List (List ℕ)) := fun R g =>
    let ins := g.inputs.map fun i => R.getD i []
    R ++ [match g.op with
      | GateOp.or => ins.foldl (fun acc A => A.foldl insertNew acc) []
      | GateOp.and => ins.foldl (andStep k) [S.map fun _ => 0]
      | _ => []]
  have hlen : ∀ (gs : List Gate) (R : List (List (List ℕ))),
      (gs.foldl rvStep R).length = R.length + gs.length := by
    intro gs R
    induction gs generalizing R with
    | nil => simp
    | cons g gs ih => rw [List.foldl_cons, ih]; simp [rvStep]; omega
  have hgetD_lt : ∀ (gs : List Gate) (R : List (List (List ℕ))) (i : ℕ),
      i < R.length → (gs.foldl rvStep R).getD i [] = R.getD i [] := by
    intro gs R i hi
    induction gs generalizing R with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons, ih (rvStep R g) (by simp [rvStep]; omega)]
      simp [rvStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
  have hstep : ∀ (gs : List Gate) (R : List (List (List ℕ))) (m : ℕ) (hm : m < gs.length),
      (gs.foldl rvStep R).getD (R.length + m) [] =
        let g := gs[m]
        let ins := g.inputs.map fun i =>
          if i < R.length + m then (gs.foldl rvStep R).getD i [] else []
        match g.op with
        | GateOp.or => ins.foldl (fun acc A => A.foldl insertNew acc) []
        | GateOp.and => ins.foldl (andStep k) [S.map fun _ => 0]
        | _ => [] := by
    intro gs R m hm
    induction gs generalizing R m with
    | nil => simp at hm
    | cons g gs ih =>
      rw [List.foldl_cons]
      cases m with
      | zero =>
        rw [Nat.add_zero, hgetD_lt gs (rvStep R g) R.length (by simp [rvStep])]
        simp only [List.getElem_cons_zero]
        have htop : (rvStep R g).getD R.length [] =
            let ins := g.inputs.map fun i => R.getD i []
            match g.op with
            | GateOp.or => ins.foldl (fun acc A => A.foldl insertNew acc) []
            | GateOp.and => ins.foldl (andStep k) [S.map fun _ => 0]
            | _ => [] := by
          simp [rvStep, List.getD_eq_getElem?_getD]
        rw [htop]
        dsimp only
        have hins : g.inputs.map (fun i => R.getD i []) =
            g.inputs.map (fun i => if i < R.length then (gs.foldl rvStep (rvStep R g)).getD i [] else []) := by
          apply List.map_congr_left
          intro i _
          by_cases hi : i < R.length
          · rw [if_pos hi, hgetD_lt gs (rvStep R g) i (by simp [rvStep]; omega)]
            simp [rvStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
          · rw [if_neg hi, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl
        rw [hins]
      | succ m =>
        have hm' : m < gs.length := by simp at hm; omega
        have ihm := ih (rvStep R g) m hm'
        have hR : (rvStep R g).length = R.length + 1 := by simp [rvStep]
        rw [hR] at ihm
        have heq : R.length + 1 + m = R.length + (m + 1) := by omega
        rw [heq] at ihm
        simpa [List.getElem_cons_succ] using ihm
  have hres := hstep C.gates ((List.range n).map (leafVectors S k)) j hj
  have hlen0 : ((List.range n).map (leafVectors S k)).length = n := by simp
  rw [hlen0] at hres
  change (readVectors C n S k).getD (n + j) [] = _ at hres
  have hgat : C.gates[j] = gateAt C j := by
    unfold gateAt; simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
  dsimp only at hres
  rw [hgat, hjor] at hres
  rw [hres]
  apply mem_foldl_or_mem _ [] ((readVectors C n S k).getD w []) _ v hv
  simp only [List.mem_map]
  refine ⟨w, hw, ?_⟩
  change (if w < n + j then (readVectors C n S k).getD w [] else []) = (readVectors C n S k).getD w []
  rw [if_pos (hrb j hj w hw)]

private lemma setList_pair {n : ℕ} (a b : Fin n) (hab : a < b) :
    setList ({a, b} : Finset (Fin n)) = [a.val, b.val] := by
  unfold setList
  have hfilt : (List.finRange n).filter (fun i => decide (i ∈ ({a, b} : Finset (Fin n)))) = [a, b] := by
    have hpw_fr : (List.finRange n).Pairwise (· < ·) := by
      rw [List.pairwise_iff_getElem]
      intro i j hi hj hij
      simpa using hij
    have hpw : ((List.finRange n).filter (fun i => decide (i ∈ ({a, b} : Finset (Fin n))))).Pairwise (· < ·) :=
      List.Pairwise.filter _ hpw_fr
    have ha : a ∈ (List.finRange n).filter (fun i => decide (i ∈ ({a, b} : Finset (Fin n)))) := by
      simp [List.mem_filter, List.mem_finRange]
    have hb : b ∈ (List.finRange n).filter (fun i => decide (i ∈ ({a, b} : Finset (Fin n)))) := by
      simp [List.mem_filter, List.mem_finRange]
    have hsub : ∀ x ∈ (List.finRange n).filter (fun i => decide (i ∈ ({a, b} : Finset (Fin n)))), x = a ∨ x = b := by
      intro x hx; simp [List.mem_filter] at hx; exact hx
    have hnd : ((List.finRange n).filter (fun i => decide (i ∈ ({a, b} : Finset (Fin n))))).Nodup :=
      hpw.imp (fun h => ne_of_lt h)
    match hl : (List.finRange n).filter (fun i => decide (i ∈ ({a, b} : Finset (Fin n)))) with
    | [] => rw [hl] at ha; simp at ha
    | [x] =>
      rw [hl] at ha hb
      simp at ha hb
      subst ha
      exact absurd hb.symm (ne_of_lt hab)
    | [x, y] =>
      rw [hl] at hpw hsub ha hb
      simp only [List.pairwise_cons, List.mem_singleton, forall_eq, List.Pairwise.nil, and_true] at hpw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · exact absurd hab (lt_irrefl _)
      · rfl
      · exact absurd (lt_trans hab hpw.1) (lt_irrefl _)
      · exact absurd hab (lt_irrefl _)
    | x :: y :: z :: rest =>
      rw [hl] at hnd
      have hx := hsub x (by rw [hl]; simp)
      have hy := hsub y (by rw [hl]; simp)
      have hz := hsub z (by rw [hl]; simp)
      have hnd3 : [x, y, z].Nodup := hnd.sublist (by simp)
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> rcases hz with rfl | rfl <;>
        simp at hnd3
  rw [hfilt]
  simp

private lemma no_cores_implies_read1 {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (D : Circuit) (hAO : IsAO2 (N + N) D)
    (hfun : circuitFun (N + N) D = graphFun (incGraph N I) ∅)
    (hnoimp : ∀ j < D.gates.length, (gateAt D j).op = GateOp.and →
      ¬ (IsImpOperand (incGraph N I) D (opnd D j 0) ∧
         IsImpOperand (incGraph N I) D (opnd D j 1)))
    (hnocore : cores (incGraph N I) D = ∅) :
    IsReadK (N + N) D 1 := by
  intro S hS
  obtain ⟨p, l, hI, rfl⟩ := prime_implicant_of_incGraph I D hfun S hS
  set u : Fin (N + N) := Fin.castAdd N p
  set v : Fin (N + N) := Fin.natAdd N l
  have huv_lt : u < v := by
    simp only [Fin.lt_def, u, v, Fin.val_castAdd, Fin.val_natAdd]
    omega
  have huv_adj : (incGraph N I).Adj u v := Or.inl ⟨p, l, hI, rfl, rfl⟩
  rw [setList_pair u v huv_lt]
  have hpi_eq : setInput ({u, v} : Finset (Fin (N + N))) = pairInput u v := by
    funext i
    simp [setInput, pairInput]
  have hout_true : wval D (pairInput u v) D.output = true := by
    have : circuitFun (N + N) D (setInput {u, v}) = true := hS.1
    rwa [hpi_eq] at this
  have hout_lt : D.output < (N + N) + D.gates.length :=
    output_lt_of_eval_true D (pairInput u v) hout_true
  have no_input_belowF : ∀ i : Fin (N + N),
      ¬ (∀ x : Fin (N + N) → Bool, wval D x i.val = true → graphFun (incGraph N I) ∅ x = true) := by
    intro i hi
    have h1 := hi (fun j => decide (j = i)) (by rw [wval_input D _ i.val i.isLt]; simp)
    rw [graphFun_incGraph] at h1
    simp only [decide_eq_true_eq] at h1
    obtain ⟨p', l', _, hp', hl'⟩ := h1
    have := congrArg Fin.val (hp'.trans hl'.symm)
    simp only [Fin.val_castAdd, Fin.val_natAdd] at this
    omega
  have hout_ge : N + N ≤ D.output := by
    by_contra hlt
    push Not at hlt
    apply no_input_belowF ⟨D.output, hlt⟩
    intro x hx
    have : circuitFun (N + N) D x = true := hx
    rwa [hfun] at this
  have hmain : ∀ j : ℕ, j < D.gates.length → BelowF (incGraph N I) D j →
      gateVal (N + N) D j (pairInput u v) = true →
      ∃ vec ∈ (readVectors D (N + N) [u.val, v.val] 1).getD ((N + N) + j) [],
        vec.all (fun a => decide (a ≤ 1)) = true := by
    intro j
    induction j using Nat.strong_induction_on with
    | ind j ih =>
      intro hj hbelow hval
      have hop : (gateAt D j).op = GateOp.and ∨ (gateAt D j).op = GateOp.or := by
        apply hAO.1
        unfold gateAt
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
        exact List.getElem_mem hj
      rcases hop with hand | hor
      · have himp : IsImpGate (incGraph N I) D j :=
          ⟨hbelow, ⟨pairInput u v, hval⟩⟩
        have hnotcore : j ∉ cores (incGraph N I) D := by
          rw [hnocore]; simp
        simp only [cores, gatesWhere, Finset.mem_filter, Finset.mem_range, not_and] at hnotcore
        have hnotrt : ¬ ReadTwiceAt (N + N) D j u v := by
          intro hrt
          exact hnotcore hj ⟨hj, himp, hnoimp j hj hand, u, v, huv_adj, hval, hrt⟩
        unfold ReadTwiceAt readsAtMost at hnotrt
        simp only [Bool.not_eq_false] at hnotrt
        rw [atGate, readVectors_output_irrel] at hnotrt
        simpa [List.any_eq_true] using hnotrt
      · have hlen2 : (gateAt D j).inputs.length = 2 := by
          apply hAO.2.2
          unfold gateAt
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
          exact List.getElem_mem hj
        have hval' : wval D (pairInput u v) (N + N + j) = true := hval
        rw [wval_gate_eval_rb D hAO.2.1 (pairInput u v) j hj, hor] at hval'
        have hin2 : (gateAt D j).inputs = [opnd D j 0, opnd D j 1] := by
          match hin : (gateAt D j).inputs with
          | [] => simp [hin] at hlen2
          | [_] => simp [hin] at hlen2
          | [a₀, a₁] => simp [opnd, hin]
          | _ :: _ :: _ :: _ => simp [hin] at hlen2
        rw [hin2] at hval'
        simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
          Bool.or_false, Bool.or_eq_true, id_eq] at hval'
        have hw0_below : ∀ x : Fin (N + N) → Bool,
            wval D x (opnd D j 0) = true → graphFun (incGraph N I) ∅ x = true := by
          intro x hx
          apply hbelow x
          change wval D x (N + N + j) = true
          rw [wval_gate_eval_rb D hAO.2.1 x j hj, hor, hin2]
          simp [GateOp.eval, hx]
        have hw1_below : ∀ x : Fin (N + N) → Bool,
            wval D x (opnd D j 1) = true → graphFun (incGraph N I) ∅ x = true := by
          intro x hx
          apply hbelow x
          change wval D x (N + N + j) = true
          rw [wval_gate_eval_rb D hAO.2.1 x j hj, hor, hin2]
          simp [GateOp.eval, hx]
        rcases hval' with h0 | h1
        · have hw0_lt : opnd D j 0 < (N + N) + j := by
            apply hAO.2.1 j hj
            rw [hin2]; simp
          have hw0_ge : N + N ≤ opnd D j 0 := by
            by_contra hlt; push Not at hlt
            exact no_input_belowF ⟨opnd D j 0, hlt⟩ hw0_below
          have hj' : opnd D j 0 - (N + N) < j := by omega
          have hbelow' : BelowF (incGraph N I) D (opnd D j 0 - (N + N)) := by
            intro x hx
            apply hw0_below x
            have heq : (N + N) + (opnd D j 0 - (N + N)) = opnd D j 0 := by omega
            rwa [← heq]
          have hval'' : gateVal (N + N) D (opnd D j 0 - (N + N)) (pairInput u v) = true := by
            change wval D (pairInput u v) ((N + N) + (opnd D j 0 - (N + N))) = true
            have heq : (N + N) + (opnd D j 0 - (N + N)) = opnd D j 0 := by omega
            rwa [heq]
          obtain ⟨vec, hvec_mem, hvec_all⟩ := ih (opnd D j 0 - (N + N)) hj' (by omega) hbelow' hval''
          have heq : (N + N) + (opnd D j 0 - (N + N)) = opnd D j 0 := by omega
          rw [heq] at hvec_mem
          refine ⟨vec, readVectors_or_subset D (N + N) [u.val, v.val] 1 hAO.2.1 j hj hor
            (opnd D j 0) (by rw [hin2]; simp) vec hvec_mem, hvec_all⟩
        · have hw1_lt : opnd D j 1 < (N + N) + j := by
            apply hAO.2.1 j hj
            rw [hin2]; simp
          have hw1_ge : N + N ≤ opnd D j 1 := by
            by_contra hlt; push Not at hlt
            exact no_input_belowF ⟨opnd D j 1, hlt⟩ hw1_below
          have hj' : opnd D j 1 - (N + N) < j := by omega
          have hbelow' : BelowF (incGraph N I) D (opnd D j 1 - (N + N)) := by
            intro x hx
            apply hw1_below x
            have heq : (N + N) + (opnd D j 1 - (N + N)) = opnd D j 1 := by omega
            rwa [← heq]
          have hval'' : gateVal (N + N) D (opnd D j 1 - (N + N)) (pairInput u v) = true := by
            change wval D (pairInput u v) ((N + N) + (opnd D j 1 - (N + N))) = true
            have heq : (N + N) + (opnd D j 1 - (N + N)) = opnd D j 1 := by omega
            rwa [heq]
          obtain ⟨vec, hvec_mem, hvec_all⟩ := ih (opnd D j 1 - (N + N)) hj' (by omega) hbelow' hval''
          have heq : (N + N) + (opnd D j 1 - (N + N)) = opnd D j 1 := by omega
          rw [heq] at hvec_mem
          refine ⟨vec, readVectors_or_subset D (N + N) [u.val, v.val] 1 hAO.2.1 j hj hor
            (opnd D j 1) (by rw [hin2]; simp) vec hvec_mem, hvec_all⟩
  have hbelow_out : BelowF (incGraph N I) D (D.output - (N + N)) := by
    intro x hx
    have heq : (N + N) + (D.output - (N + N)) = D.output := by omega
    have hx' : circuitFun (N + N) D x = true := by
      change wval D x D.output = true
      rw [← heq]; exact hx
    rwa [hfun] at hx'
  have hval_out : gateVal (N + N) D (D.output - (N + N)) (pairInput u v) = true := by
    change wval D (pairInput u v) ((N + N) + (D.output - (N + N))) = true
    have heq : (N + N) + (D.output - (N + N)) = D.output := by omega
    rwa [heq]
  obtain ⟨vec, hvec_mem, hvec_all⟩ := hmain (D.output - (N + N)) (by omega) hbelow_out hval_out
  have heq : (N + N) + (D.output - (N + N)) = D.output := by omega
  rw [heq] at hvec_mem
  unfold readsAtMost
  rw [List.any_eq_true]
  exact ⟨vec, hvec_mem, hvec_all⟩

private lemma no_belowF_operand_of_least {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hne : G.edgeFinset.Nonempty) (C : Circuit) (hleast : IsLeastAO G C)
    (j : ℕ) (hj : j < C.gates.length) (hjand : (gateAt C j).op = GateOp.and)
    (w : ℕ) (hw : w ∈ (gateAt C j).inputs) :
    ¬ (∀ x : Fin n → Bool, wval C x w = true → graphFun G ∅ x = true) := by
  intro hwbelow
  have hAO := hleast.1
  have hfun := hleast.2.1
  have hwlt : w < n + j := hAO.2.1 j hj w hw
  have hE_AO := eraseGate_isAO2 C j w hAO hj hwlt
  have hE_len := eraseGate_length (n := n) C j w hj
  have hout : C.output < n + C.gates.length := by
    obtain ⟨e, he⟩ := hne
    induction e using Sym2.ind with
    | _ u v =>
      have huv : G.Adj u v := SimpleGraph.mem_edgeFinset.mp he
      have htrue : circuitFun n C (pairInput u v) = true := by
        rw [hfun]
        simp [graphFun, pairInput]
        exact ⟨u, v, huv, Or.inl rfl, Or.inr rfl⟩
      exact output_lt_of_eval_true C (pairInput u v) htrue
  have hstep : ∀ (x : Fin n → Bool) (k : ℕ), k < C.gates.length → k ≠ j →
      (wval C x (n + k) = true →
        wval (eraseGate n C j w) x (n + (if k < j then k else k - 1)) = true) ∧
      (graphFun G ∅ x = false →
        wval (eraseGate n C j w) x (n + (if k < j then k else k - 1)) = wval C x (n + k)) := by
    intro x k
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      intro hk hkne
      by_cases hkj : k < j
      · rw [if_pos hkj]
        have heq : wval (eraseGate n C j w) x (n + k) = wval C x (n + k) :=
          wval_eraseGate_lt C j w hj x (n + k) (by omega)
        rw [heq]
        exact ⟨id, fun _ => rfl⟩
      · have hjk : j < k := by omega
        rw [if_neg hkj]
        have hk1 : k - 1 < (eraseGate n C j w).gates.length := by omega
        have heq1 : (k - 1) + 1 = k := by omega
        have hwireE := wval_gate_eval_rb (eraseGate n C j w) hE_AO.2.1 x (k - 1) hk1
        have hwireC := wval_gate_eval_rb C hAO.2.1 x k hk
        rw [gateAt_eraseGate_ge C j w (k - 1) hj (by omega) (by omega), heq1] at hwireE
        have hop : (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or := by
          apply hAO.1
          unfold gateAt
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
          exact List.getElem_mem hk
        constructor
        · intro htrue
          rw [hwireC] at htrue
          rw [hwireE, List.map_map]
          apply gateOp_mono (gateAt C k).op hop (by simp) _ htrue
          intro i hi hval
          simp only [List.length_map] at hi
          simp only [List.getElem_map, Function.comp_apply] at hval ⊢
          set u := (gateAt C k).inputs[i]
          have hult : u < n + k := hAO.2.1 k hk u (List.getElem_mem hi)
          unfold eraseRedirect
          split_ifs with hu1 hu2
          · rw [hu1, wval_gate_eval_rb C hAO.2.1 x j hj, hjand] at hval
            simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq, forall_exists_index,
              and_imp, forall_apply_eq_imp_iff₂] at hval
            rw [wval_eraseGate_lt C j w hj x w hwlt]
            exact hval w hw
          · have hsub : u - n < k ∧ u - n ≠ j := ⟨by omega, by omega⟩
            have hi_sub := (ih (u - n) hsub.1 (by omega) hsub.2).1
            have hidx : (if u - n < j then u - n else u - n - 1) = u - n - 1 := by
              simp [show ¬ u - n < j by omega]
            have hu_eq : n + (u - n - 1) = u - 1 := by omega
            have hu_eq2 : n + (u - n) = u := by omega
            rw [hidx, hu_eq] at hi_sub
            rw [hu_eq2] at hi_sub
            exact hi_sub hval
          · rw [wval_eraseGate_lt C j w hj x u (by omega)]
            exact hval
        · intro hgf
          rw [hwireE, hwireC, List.map_map]
          congr 1
          apply List.map_congr_left
          intro u hu
          have hult : u < n + k := hAO.2.1 k hk u hu
          simp only [Function.comp_apply]
          unfold eraseRedirect
          split_ifs with hu1 hu2
          · rw [hu1, wval_eraseGate_lt C j w hj x w hwlt]
            have hwf : wval C x w = false := by
              by_contra hwt
              simp only [Bool.not_eq_false] at hwt
              have := hwbelow x hwt
              rw [this] at hgf; cases hgf
            have hjf : wval C x (n + j) = false := by
              by_contra hjt
              simp only [Bool.not_eq_false] at hjt
              rw [wval_gate_eval_rb C hAO.2.1 x j hj, hjand] at hjt
              simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq, forall_exists_index,
                and_imp, forall_apply_eq_imp_iff₂] at hjt
              rw [hjt w hw] at hwf; cases hwf
            rw [hwf, hjf]
          · have hi_sub := (ih (u - n) (by omega) (by omega) (by omega)).2 hgf
            have hidx : (if u - n < j then u - n else u - n - 1) = u - n - 1 := by
              simp [show ¬ u - n < j by omega]
            have hu_eq : n + (u - n - 1) = u - 1 := by omega
            have hu_eq2 : n + (u - n) = u := by omega
            rw [hidx, hu_eq, hu_eq2] at hi_sub
            exact hi_sub
          · exact wval_eraseGate_lt C j w hj x u (by omega)
  have hE_fun : circuitFun n (eraseGate n C j w) = graphFun G ∅ := by
    funext x
    have hEout : (eraseGate n C j w).output = eraseRedirect n j w C.output := by
      unfold eraseGate; rw [if_pos hj]
    have hcfE : circuitFun n (eraseGate n C j w) x = wval (eraseGate n C j w) x (eraseRedirect n j w C.output) := by
      change wval (eraseGate n C j w) x (eraseGate n C j w).output = _
      rw [hEout]
    rw [hcfE]
    by_cases hgx : graphFun G ∅ x = true
    · rw [hgx]
      have hCx : wval C x C.output = true := by
        change circuitFun n C x = true; rw [hfun]; exact hgx
      unfold eraseRedirect
      split_ifs with h1 h2
      · rw [h1, wval_gate_eval_rb C hAO.2.1 x j hj, hjand] at hCx
        simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq, forall_exists_index,
          and_imp, forall_apply_eq_imp_iff₂] at hCx
        rw [wval_eraseGate_lt C j w hj x w hwlt]
        exact hCx w hw
      · have hst := (hstep x (C.output - n) (by omega) (by omega)).1
        rw [if_neg (by omega)] at hst
        have heq1 : n + (C.output - n - 1) = C.output - 1 := by omega
        have heq2 : n + (C.output - n) = C.output := by omega
        rw [heq1, heq2] at hst
        exact hst hCx
      · rw [wval_eraseGate_lt C j w hj x C.output (by omega)]
        exact hCx
    · have hgf : graphFun G ∅ x = false := Bool.eq_false_iff.mpr hgx
      rw [hgf]
      have hCx : wval C x C.output = false := by
        change circuitFun n C x = false; rw [hfun]; exact hgf
      unfold eraseRedirect
      split_ifs with h1 h2
      · rw [wval_eraseGate_lt C j w hj x w hwlt]
        by_contra hwt
        simp only [Bool.not_eq_false] at hwt
        have := hwbelow x hwt
        rw [this] at hgf; cases hgf
      · have hst := (hstep x (C.output - n) (by omega) (by omega)).2 hgf
        rw [if_neg (by omega)] at hst
        have heq1 : n + (C.output - n - 1) = C.output - 1 := by omega
        have heq2 : n + (C.output - n) = C.output := by omega
        rw [heq1, heq2] at hst
        rw [hst, hCx]
      · rw [wval_eraseGate_lt C j w hj x C.output (by omega)]
        exact hCx
  have hle := hleast.2.2 (eraseGate n C j w) hE_AO hE_fun
  change C.gates.length ≤ (eraseGate n C j w).gates.length at hle
  omega

/-! Final reduction: L-meta-2583 reduced to core-freeness of minimal lift-fixed-points -/

theorem reduction_to_core_free
    (core_free : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit),
      2 ≤ q → N = q ^ 2 + q + 1 →
      (∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1) →
      (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) →
      IsLeastAO (incGraph N I) C →
      IsLiftFixedPoint (incGraph N I) C →
      (∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
        ¬ (IsImpOperand (incGraph N I) C (opnd C j 0) ∧
           IsImpOperand (incGraph N I) C (opnd C j 1))) →
      cores (incGraph N I) C = ∅) :
    ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit),
      2 ≤ q → N = q ^ 2 + q + 1 →
      (∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1) →
      (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) →
      IsAO2 (N + N) C →
      (∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z =
        decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)) →
      ∃ D : Circuit, IsAO2 (N + N) D ∧
        (∀ y : Fin (N + N) → Bool, circuitFun (N + N) D y =
          decide (∃ p l : Fin N, I p l ∧ y (Fin.castAdd N p) = true ∧ y (Fin.natAdd N l) = true)) ∧
        D.size ≤ C.size ∧ IsReadK (N + N) D 1 := by
  intro q N I _ C hq hN hcard hline hAO hfun
  have hfun' : circuitFun (N + N) C = graphFun (incGraph N I) ∅ := by
    funext z; rw [hfun z, graphFun_incGraph]
  have hne : (incGraph N I).edgeFinset.Nonempty := by
    have hNpos : 0 < N := by subst hN; exact Nat.succ_pos _
    let l0 : Fin N := ⟨0, hNpos⟩
    have hc := hcard l0
    obtain ⟨p, hp⟩ : (Finset.univ.filter (fun p => I p l0)).Nonempty := by
      rw [← Finset.card_pos, hc]; omega
    have hI := (Finset.mem_filter.1 hp).2
    refine ⟨s(Fin.castAdd N p, Fin.natAdd N l0), ?_⟩
    rw [SimpleGraph.mem_edgeFinset]
    exact Or.inl ⟨p, l0, hI, rfl, rfl⟩
  obtain ⟨C', hleast, hsz', hfp'⟩ := exists_leastAO (incGraph N I) hne C hAO hfun'
  have hnoimp : ∀ j < C'.gates.length, (gateAt C' j).op = GateOp.and →
      ¬ (IsImpOperand (incGraph N I) C' (opnd C' j 0) ∧
         IsImpOperand (incGraph N I) C' (opnd C' j 1)) := by
    intro j hj hand ⟨h0, _⟩
    have hlen2 : (gateAt C' j).inputs.length = 2 := by
      apply hleast.1.2.2
      unfold gateAt
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
      exact List.getElem_mem hj
    have hop0_mem : opnd C' j 0 ∈ (gateAt C' j).inputs := by
      simp [opnd, List.getD_eq_getElem?_getD]
      rw [List.getElem?_eq_getElem (by omega)]
      exact List.getElem_mem _
    apply no_belowF_operand_of_least (incGraph N I) hne C' hleast j hj hand (opnd C' j 0) hop0_mem
    intro x hx
    have hsub := h0.2.1 x
    apply hsub
    change wval C' x ((N + N) + (opnd C' j 0 - (N + N))) = true
    have heq : (N + N) + (opnd C' j 0 - (N + N)) = opnd C' j 0 := by
      have := h0.1; omega
    rwa [heq]
  have hnocore := core_free q N I C' hq hN hcard hline hleast hfp' hnoimp
  have hread1 := no_cores_implies_read1 I C' hleast.1 hleast.2.1 hnoimp hnocore
  refine ⟨C', hleast.1, ?_, hsz', hread1⟩
  intro y
  rw [congrFun hleast.2.1 y, graphFun_incGraph]



end PEqualNP.Outside.R_meta_2583_1

open Classical

theorem PEqualNP.Outside.R_meta_2583_1
    (core_free : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit),
      2 ≤ q → N = q ^ 2 + q + 1 →
      (∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1) →
      (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) →
      PEqualNP.TopForm.IsLeastAO (PEqualNP.Outside.R_meta_2583_1.incGraph N I) C →
      PEqualNP.Core.IsLiftFixedPoint (PEqualNP.Outside.R_meta_2583_1.incGraph N I) C →
      (∀ j < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and →
        ¬ (PEqualNP.Core.IsImpOperand (PEqualNP.Outside.R_meta_2583_1.incGraph N I) C (PEqualNP.TopForm.opnd C j 0) ∧
           PEqualNP.Core.IsImpOperand (PEqualNP.Outside.R_meta_2583_1.incGraph N I) C (PEqualNP.TopForm.opnd C j 1))) →
      PEqualNP.Core.cores (PEqualNP.Outside.R_meta_2583_1.incGraph N I) C = ∅) :
    ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit),
      2 ≤ q → N = q ^ 2 + q + 1 →
      (∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1) →
      (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) →
      PEqualNP.TopForm.IsAO2 (N + N) C →
      (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) C z =
        decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)) →
      ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 (N + N) D ∧
        (∀ y : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) D y =
          decide (∃ p l : Fin N, I p l ∧ y (Fin.castAdd N p) = true ∧ y (Fin.natAdd N l) = true)) ∧
        D.size ≤ C.size ∧ PEqualNP.ReadK.IsReadK (N + N) D 1 :=
  PEqualNP.Outside.R_meta_2583_1.reduction_to_core_free core_free
