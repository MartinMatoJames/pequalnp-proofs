import PEqualNP.Defs

-- The search engine is adapted from PEqualNP.Outside.L_meta_1673 by Trey Kind (pull request 6929, Apache License 2.0).
-- This file declares its own data types (records for the search state and inductive predicates).

namespace PEqualNP.Outside.L_meta_11040
variable {R : ℕ → ℕ}
def op (d : Bool) (a b : ℕ) : ℕ := bif d then a ||| b else a &&& b
lemma op_comm (d : Bool) (a b : ℕ) : op d a b = op d b a := by
  cases d <;> simp [op, Nat.and_comm, Nat.or_comm]
lemma op_bit (d : Bool) (a b i : ℕ) : (op d a b).testBit i =
    bif d then a.testBit i || b.testBit i else a.testBit i && b.testBit i := by
  cases d <;> simp [op]
lemma op_self (d : Bool) (a : ℕ) : op d a a = a := by cases d <;> simp [op]
def Al (R : ℕ → ℕ) (d : Bool) (a b : ℕ) : Prop := (R a &&& R b) ≤ (bif d then 1 else 0)
lemma Al.symm {d : Bool} {a b : ℕ} (h : Al R d a b) : Al R d b a := by unfold Al at *; rwa [Nat.and_comm]
def Z0 : ℕ → ℕ := fun _ => 0
lemma al0 (d : Bool) (a b : ℕ) : Al Z0 d a b := by simp [Al, Z0]
inductive Sol (R : ℕ → ℕ) (m T : ℕ) : ℕ → Set ℕ → Prop
  | done {q : ℕ} {S : Set ℕ} : T ∈ S → Sol R m T q S
  | un {q : ℕ} {S : Set ℕ} {a : ℕ} : a ∈ S → Sol R m T q (insert (a ^^^ m) S) → Sol R m T (q + 1) S
  | bi {q : ℕ} {S : Set ℕ} {d : Bool} {a b : ℕ} : a ∈ S → b ∈ S → Al R d a b →
      Sol R m T q (insert (op d a b) S) → Sol R m T (q + 1) S
lemma Sol.mono {m T q : ℕ} {S : Set ℕ} (h : Sol R m T q S) :
    ∀ {q' : ℕ} {S' : Set ℕ}, q ≤ q' → S ⊆ S' → Sol R m T q' S' := by
  induction h with
  | done h => intro q' S' _ hs; exact .done (hs h)
  | un h _ ih =>
    intro q' S' hq hs
    obtain ⟨r, rfl⟩ : ∃ r, q' = r + 1 := ⟨q' - 1, by omega⟩
    exact .un (hs h) (ih (by omega) (Set.insert_subset_insert hs))
  | bi h1 h2 ha _ ih =>
    intro q' S' hq hs
    obtain ⟨r, rfl⟩ : ∃ r, q' = r + 1 := ⟨q' - 1, by omega⟩
    exact .bi (hs h1) (hs h2) ha (ih (by omega) (Set.insert_subset_insert hs))
lemma Sol.rel {R' : ℕ → ℕ} {m T q : ℕ} {S : Set ℕ} (h : Sol R m T q S) (hR : ∀ d a b, Al R d a b → Al R' d a b) : Sol R' m T q S := by
  induction h with
  | done h => exact .done h
  | un h _ ih => exact .un h ih
  | bi h1 h2 ha _ ih => exact .bi h1 h2 (hR _ _ _ ha) ih
lemma Sol.to0 {m T q : ℕ} {S : Set ℕ} (h : Sol R m T q S) : Sol Z0 m T q S := h.rel fun d a b _ => al0 d a b
inductive Live (R : ℕ → ℕ) (m T : ℕ) : ℕ → ℕ → Finset ℕ → Prop
  | stop : Live R m T 0 0 {T}
  | un {k t : ℕ} {a : ℕ} {U : Finset ℕ} : Live R m T k t (insert (a ^^^ m) U) →
      Live R m T (k + 1) (t + 1) (insert a U)
  | bi {k t : ℕ} {d : Bool} {a b : ℕ} {U : Finset ℕ} : a ≠ b → Al R d a b → Live R m T k t (insert (op d a b) U) →
      Live R m T (k + 1) t (insert a (insert b U))
lemma Live.sol {m T k t : ℕ} {S : Finset ℕ} (h : Live R m T k t S) : Sol Z0 m T k (S : Set ℕ) := by
  induction h with
  | stop => exact .done (by simp)
  | @un k t a U _ ih =>
    refine .un (a := a) (by simp) (ih.mono le_rfl ?_)
    intro x hx; simp at hx ⊢; tauto
  | @bi k t d a b U _ _ _ ih =>
    refine .bi (d := d) (a := a) (b := b) (by simp) (by simp) (al0 _ _ _) (ih.mono le_rfl ?_)
    intro x hx; simp at hx ⊢; tauto
lemma Sol.live {m T q : ℕ} {S : Set ℕ} (h : Sol R m T q S) :
    ∃ k ≤ q, ∃ t, ∃ S0 : Finset ℕ, (S0 : Set ℕ) ⊆ S ∧ Live R m T k t S0 := by
  induction h with
  | @done q S h => exact ⟨0, by omega, 0, {T}, by simpa using h, .stop⟩
  | @un q S a ha _ ih =>
    obtain ⟨k, hk, t, S1, hs, hl⟩ := ih
    by_cases hg : a ^^^ m ∈ S1
    · refine ⟨k + 1, by omega, t + 1, insert a (S1.erase (a ^^^ m)), ?_, .un (by rwa [Finset.insert_erase hg])⟩
      intro x hx
      simp at hx
      rcases hx with rfl | ⟨h1, h2⟩
      · exact ha
      · exact (hs h1).resolve_left h2
    · exact ⟨k, by omega, t, S1, fun x hx => (hs hx).resolve_left (fun e => hg (e ▸ hx)), hl⟩
  | @bi q S d a b ha hb hal _ ih =>
    obtain ⟨k, hk, t, S1, hs, hl⟩ := ih
    by_cases hg : op d a b ∈ S1
    · by_cases hab : a = b
      · subst hab; rw [op_self] at hs
        exact ⟨k, by omega, t, S1, fun x hx => (hs hx).elim (fun e => e ▸ ha) id, hl⟩
      refine ⟨k + 1, by omega, t, insert a (insert b (S1.erase (op d a b))), ?_, .bi hab hal (by rwa [Finset.insert_erase hg])⟩
      intro x hx
      simp at hx
      rcases hx with rfl | rfl | ⟨h1, h2⟩
      · exact ha
      · exact hb
      · exact (hs h1).resolve_left h2
    · exact ⟨k, by omega, t, S1, fun x hx => (hs hx).resolve_left (fun e => hg (e ▸ hx)), hl⟩
def C (m : ℕ) (S : Set ℕ) : Set ℕ := S ∪ {0, m}
lemma C_mono {m : ℕ} {S S' : Set ℕ} (h : S ⊆ S') : C m S ⊆ C m S' := Set.union_subset_union_left _ h
lemma sub_C (m : ℕ) (S : Set ℕ) : S ⊆ C m S := Set.subset_union_left
def Un (m a : ℕ) (S S' : Finset ℕ) : Prop := ∃ U, S = insert a U ∧ S' = insert (a ^^^ m) U
def Bi (R : ℕ → ℕ) (d : Bool) (a b : ℕ) (S S' : Finset ℕ) : Prop :=
  a ≠ b ∧ ∃ U, S = insert a (insert b U) ∧ S' = insert (op d a b) U ∧ Al R d a b
lemma Un.live {m T a k t : ℕ} {S S' : Finset ℕ} (h : Un m a S S') (hl : Live R m T k t S') :
    Live R m T (k + 1) (t + 1) S := by obtain ⟨U, rfl, rfl⟩ := h; exact .un hl
lemma Bi.live {m T a b k t : ℕ} {d : Bool} {S S' : Finset ℕ} (h : Bi R d a b S S') (hl : Live R m T k t S') :
    Live R m T (k + 1) t S := by obtain ⟨hab, U, rfl, rfl, hal⟩ := h; exact .bi hab hal hl
lemma Bi.symm {a b : ℕ} {d : Bool} {S S' : Finset ℕ} (h : Bi R d a b S S') : Bi R d b a S S' := by
  obtain ⟨hab, U, rfl, rfl, hal⟩ := h
  exact ⟨hab.symm, U, Finset.insert_comm _ _ _, by rw [op_comm], hal.symm⟩
lemma Un.sub {m a : ℕ} {S S' : Finset ℕ} (h : Un m a S S') : a ∈ S ∧ S' ⊆ insert (a ^^^ m) S := by
  obtain ⟨U, rfl, rfl⟩ := h
  exact ⟨by simp, Finset.insert_subset_insert _ (Finset.subset_insert _ _)⟩
lemma Bi.sub {a b : ℕ} {d : Bool} {S S' : Finset ℕ} (h : Bi R d a b S S') :
    a ∈ S ∧ b ∈ S ∧ S' ⊆ insert (op d a b) S := by
  obtain ⟨_, U, rfl, rfl, _⟩ := h
  refine ⟨by simp, by simp, Finset.insert_subset_insert _ ?_⟩
  intro x hx; simp [hx]
def Min (R : ℕ → ℕ) (m T k t : ℕ) (S : Finset ℕ) : Prop := Live R m T k t S ∧ ∀ q < k, ¬ Sol Z0 m T q (C m S)
lemma Un.sol {m T a q : ℕ} {S S' : Finset ℕ} (h : Un m a S S') (hs : Sol Z0 m T q (C m S')) :
    Sol Z0 m T (q + 1) (C m S) := by
  obtain ⟨ha, hsub⟩ := h.sub
  refine .un (a := a) (sub_C _ _ (by simpa using ha)) (hs.mono le_rfl ?_)
  intro x hx
  rcases hx with hx | hx
  · have := hsub hx; simp at this
    rcases this with rfl | h'
    · exact Or.inl rfl
    · exact Or.inr (Or.inl h')
  · exact Or.inr (Or.inr hx)
lemma Bi.sol {m T a b q : ℕ} {d : Bool} {S S' : Finset ℕ} (h : Bi R d a b S S') (hs : Sol Z0 m T q (C m S')) :
    Sol Z0 m T (q + 1) (C m S) := by
  obtain ⟨ha, hb, hsub⟩ := h.sub
  refine .bi (d := d) (a := a) (b := b) (sub_C _ _ (by simpa using ha)) (sub_C _ _ (by simpa using hb)) (al0 _ _ _) (hs.mono le_rfl ?_)
  intro x hx
  rcases hx with hx | hx
  · have := hsub hx; simp at this
    rcases this with rfl | h'
    · exact Or.inl rfl
    · exact Or.inr (Or.inl h')
  · exact Or.inr (Or.inr hx)
lemma Un.min {m T a k t : ℕ} {S S' : Finset ℕ} (h : Un m a S S') (hl : Live R m T k t S')
    (hm : ∀ q < k + 1, ¬ Sol Z0 m T q (C m S)) : Min R m T k t S' :=
  ⟨hl, fun q hq hs => hm (q + 1) (by omega) (h.sol hs)⟩
lemma Bi.min {m T a b k t : ℕ} {d : Bool} {S S' : Finset ℕ} (h : Bi R d a b S S') (hl : Live R m T k t S')
    (hm : ∀ q < k + 1, ¬ Sol Z0 m T q (C m S)) : Min R m T k t S' :=
  ⟨hl, fun q hq hs => hm (q + 1) (by omega) (h.sol hs)⟩
lemma Un.fresh {m T a k t : ℕ} {S S' : Finset ℕ} (h : Un m a S S') (hl : Live R m T k t S')
    (hm : ∀ q < k + 1, ¬ Sol Z0 m T q (C m S)) : a ^^^ m ∉ C m S := by
  intro hg
  apply hm k (by omega)
  refine hl.sol.mono le_rfl fun x hx => ?_
  have := h.sub.2 hx; simp at this
  rcases this with rfl | h'
  · exact hg
  · exact Or.inl h'
lemma Bi.fresh {m T a b k t : ℕ} {d : Bool} {S S' : Finset ℕ} (h : Bi R d a b S S') (hl : Live R m T k t S')
    (hm : ∀ q < k + 1, ¬ Sol Z0 m T q (C m S)) : op d a b ∉ C m S := by
  intro hg
  apply hm k (by omega)
  refine hl.sol.mono le_rfl fun x hx => ?_
  have := h.sub.2.2 hx; simp at this
  rcases this with rfl | h'
  · exact hg
  · exact Or.inl h'
lemma Min.size {m T : ℕ} : ∀ {k t : ℕ} {S : Finset ℕ}, Min R m T k t S → S.card + t ≤ k + 1 ∧ t ≤ k := by
  intro k t S ⟨hl, hm⟩
  induction hl with
  | stop => simp
  | @un k t a U hl ih =>
    have hu : Un m a (insert a U) (insert (a ^^^ m) U) := ⟨U, rfl, rfl⟩
    have ih := ih (hu.min hl hm).2
    have hf : a ^^^ m ∉ U := fun h => hu.fresh hl hm (sub_C _ _ (by simp [h]))
    have h1 := Finset.card_insert_le a U
    rw [Finset.card_insert_of_notMem hf] at ih; omega
  | @bi k t d a b U hab hal hl ih =>
    have hu : Bi R d a b (insert a (insert b U)) (insert (op d a b) U) := ⟨hab, U, rfl, rfl, hal⟩
    have ih := ih (hu.min hl hm).2
    have hf : op d a b ∉ U := fun h => hu.fresh hl hm (sub_C _ _ (by simp [h]))
    have h1 := Finset.card_insert_le a (insert b U)
    have h2 := Finset.card_insert_le b U
    rw [Finset.card_insert_of_notMem hf] at ih; omega
def phi (a n : ℕ) (X : Finset ℕ) : Finset ℕ := insert a (X.erase n)
lemma phi_un {m a n c : ℕ} {X X' : Finset ℕ} (h : Un m c X X') (h1 : c ≠ n) (h2 : c ^^^ m ≠ n) :
    Un m c (phi a n X) (phi a n X') := by
  obtain ⟨U, rfl, rfl⟩ := h
  refine ⟨insert a (U.erase n), ?_, ?_⟩ <;> ext x <;> simp [phi] <;> grind
lemma phi_bi {a n b c : ℕ} {d : Bool} {X X' : Finset ℕ} (h : Bi R d b c X X') (h1 : b ≠ n) (h2 : c ≠ n)
    (h3 : op d b c ≠ n) : Bi R d b c (phi a n X) (phi a n X') := by
  obtain ⟨hab, U, rfl, rfl, hal⟩ := h
  refine ⟨hab, insert a (U.erase n), ?_, ?_, hal⟩ <;> ext x <;> simp [phi] <;> grind
lemma phi_back {m a : ℕ} {X : Finset ℕ} (h : a ^^^ m ∈ X) : Un m a (phi a (a ^^^ m) X) X :=
  ⟨X.erase (a ^^^ m), rfl, by rw [Finset.insert_erase h]⟩
lemma phi_start {m a : ℕ} {S S' : Finset ℕ} (h : Un m a S S') (hn : a ^^^ m ∉ S) : phi a (a ^^^ m) S' = S := by
  obtain ⟨U, rfl, rfl⟩ := h
  simp at hn
  simp [phi, hn.2]
lemma un_keep {m c n : ℕ} {X X' : Finset ℕ} (h : Un m c X X') (hn : n ∈ X) (h1 : c ≠ n) : n ∈ X' := by
  obtain ⟨U, rfl, rfl⟩ := h
  simp at hn ⊢; exact Or.inr (hn.resolve_left (Ne.symm h1))
lemma bi_keep {b c n : ℕ} {d : Bool} {X X' : Finset ℕ} (h : Bi R d b c X X') (hn : n ∈ X) (h1 : b ≠ n)
    (h2 : c ≠ n) : n ∈ X' := by
  obtain ⟨_, U, rfl, rfl, _⟩ := h
  simp at hn ⊢; rcases hn with h | h | h
  · exact absurd h.symm h1
  · exact absurd h.symm h2
  · exact Or.inr h
lemma first_move {m T : ℕ} : ∀ (k t : ℕ) (S : Finset ℕ), Min R m T k t S → 2 ≤ S.card →
    (∃ k0 d a b S1, k = k0 + 1 ∧ Bi R d a b S S1 ∧ Live R m T k0 t S1) ∨
    (∃ k0 t0 a d c S1 S2, k = k0 + 2 ∧ t = t0 + 1 ∧ Un m a S S1 ∧ Bi R d (a ^^^ m) c S1 S2 ∧ Live R m T k0 t0 S2) ∨
    (∃ k0 t0 a a' d S1 S2 S3, k = k0 + 3 ∧ t = t0 + 2 ∧ Un m a S S1 ∧ a' ≠ a ^^^ m ∧ Un m a' S1 S2 ∧
      Bi R d (a ^^^ m) (a' ^^^ m) S2 S3 ∧ Live R m T k0 t0 S3) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro t S hS hc
  obtain ⟨hl, hm⟩ := hS
  cases hl with
  | stop => simp at hc
  | @bi k t d a b U hab hal hl => exact Or.inl ⟨k, d, a, b, _, rfl, ⟨hab, U, rfl, rfl, hal⟩, hl⟩
  | @un k t a U hl =>
    have hu : Un m a (insert a U) (insert (a ^^^ m) U) := ⟨U, rfl, rfl⟩
    have hf := hu.fresh hl hm
    have hn : a ^^^ m ∉ insert a U := fun h => hf (sub_C _ _ (by simpa using h))
    have hmin := hu.min hl hm
    have hxx : ∀ c : ℕ, c ^^^ m ^^^ m = c := fun c => by simp
    have hc' : 2 ≤ (insert (a ^^^ m) U).card := by
      have h1 := Finset.card_insert_le a U
      rw [Finset.card_insert_of_notMem (fun h => hn (by simp [h]))]; omega
    generalize hS1 : insert (a ^^^ m) U = S1 at *
    have hnS1 : a ^^^ m ∈ S1 := by rw [← hS1]; simp
    have hst := phi_start hu hn
    have dbl : ∀ {c k2 t2 S2}, Un m c S1 S2 → Live R m T k2 t2 S2 → k = k2 + 1 → c ≠ a ^^^ m ∧ c ^^^ m ≠ a ^^^ m := by
      intro c k2 t2 S2 h2 hl2 hk
      constructor
      · rintro rfl
        have hsub := h2.sub.2
        rw [hxx] at hsub
        apply hm (k2 + 1) (by omega)
        refine .un (a := a) (sub_C _ _ (by simp)) (hl2.sol.mono le_rfl fun x hx => ?_)
        have h3 := hsub hx
        have h4 : x ∈ insert a (insert (a ^^^ m) U) := by rw [hS1]; exact h3
        simp at h4
        rcases h4 with rfl | rfl | h4
        · exact Or.inr (sub_C _ _ (by simp))
        · exact Or.inl rfl
        · exact Or.inr (sub_C _ _ (by simp [h4]))
      · intro e
        exact h2.fresh hl2 (by rw [← hk]; exact hmin.2) (sub_C _ _ (by rw [e]; simpa using hnS1))
    rcases ih k (by omega) t S1 hmin hc' with
      ⟨k0, d, x, y, S2, rfl, hb, hl2⟩ | ⟨k0, t0, c, d, y, S2, S3, rfl, rfl, h1, hb, hl2⟩ |
      ⟨k0, t0, c, c', d, S2, S3, S4, rfl, rfl, h1, hne, h2, hb, hl2⟩
    · by_cases hx : x = a ^^^ m
      · subst hx; exact Or.inr (Or.inl ⟨k0, t, a, d, y, S1, S2, rfl, rfl, hu, hb, hl2⟩)
      by_cases hy : y = a ^^^ m
      · subst hy; exact Or.inr (Or.inl ⟨k0, t, a, d, x, S1, S2, rfl, rfl, hu, hb.symm, hl2⟩)
      have hg : op d x y ≠ a ^^^ m := fun e => hb.fresh hl2 hmin.2 (sub_C _ _ (by rw [e]; simpa using hnS1))
      refine Or.inl ⟨k0 + 1, d, x, y, phi a (a ^^^ m) S2, rfl, ?_, ?_⟩
      · rw [← hst]; exact phi_bi hb hx hy hg
      · exact (phi_back (bi_keep hb hnS1 hx hy)).live hl2
    · have hb1 := hb.live hl2
      obtain ⟨n1, n2⟩ := dbl h1 hb1 rfl
      have hm2 := h1.min hb1 hmin.2
      by_cases hy : y = a ^^^ m
      · subst hy
        exact Or.inr (Or.inr ⟨k0, t0, a, c, d, S1, S2, S3, rfl, rfl, hu, n1, h1, hb.symm, hl2⟩)
      have hk2 := un_keep h1 hnS1 n1
      have hg : op d (c ^^^ m) y ≠ a ^^^ m := fun e => hb.fresh hl2 hm2.2 (sub_C _ _ (by rw [e]; simpa using hk2))
      refine Or.inr (Or.inl ⟨k0 + 1, t0 + 1, c, d, y, phi a (a ^^^ m) S2, phi a (a ^^^ m) S3, rfl, rfl, ?_, phi_bi hb n2 hy hg, ?_⟩)
      · rw [← hst]; exact phi_un h1 n1 n2
      · exact (phi_back (bi_keep hb hk2 n2 hy)).live hl2
    · have hb1 := hb.live hl2
      have hb2 := h2.live hb1
      obtain ⟨n1, n2⟩ := dbl h1 hb2 rfl
      have hm2 := h1.min hb2 hmin.2
      have hk2 := un_keep h1 hnS1 n1
      have hm3 := h2.min hb1 hm2.2
      have n3 : c' ≠ a ^^^ m := by
        rintro rfl
        have hsub := h2.sub.2
        rw [hxx] at hsub
        obtain ⟨hcS, hsub1⟩ := h1.sub
        have hcS' : c ∈ insert a U := by
          have : c ∈ insert (a ^^^ m) U := by rw [hS1]; exact hcS
          simp at this ⊢; exact Or.inr (this.resolve_left n1)
        apply hm (k0 + 1 + 1 + 1) (by omega)
        refine .un (a := a) (sub_C _ _ (by simp)) (.un (a := c) (Or.inr (sub_C _ _ (by simpa using hcS'))) (hb1.sol.mono le_rfl fun x hx => ?_))
        have h3 : x = a ∨ x = c ^^^ m ∨ x ∈ S1 := by
          have := hsub hx; simp at this
          rcases this with h | h
          · exact Or.inl h
          · have := hsub1 h; simp at this; exact Or.inr this
        rcases h3 with rfl | rfl | h3
        · exact Or.inr (Or.inr (sub_C _ _ (by simp)))
        · exact Or.inl rfl
        · rw [← hS1] at h3; simp at h3
          rcases h3 with rfl | h3
          · exact Or.inr (Or.inl rfl)
          · exact Or.inr (Or.inr (sub_C _ _ (by simp [h3])))
      have n4 : c' ^^^ m ≠ a ^^^ m := fun e => h2.fresh hb1 hm2.2 (sub_C _ _ (by rw [e]; simpa using hk2))
      have hk3 := un_keep h2 hk2 n3
      have hg : op d (c ^^^ m) (c' ^^^ m) ≠ a ^^^ m := fun e => hb.fresh hl2 hm3.2 (sub_C _ _ (by rw [e]; simpa using hk3))
      refine Or.inr (Or.inr ⟨k0 + 1, t0 + 1, c, c', d, phi a (a ^^^ m) S2, phi a (a ^^^ m) S3, phi a (a ^^^ m) S4, rfl, rfl, ?_, hne,
        phi_un h2 n3 n4, phi_bi hb n2 n4 hg, ?_⟩)
      · rw [← hst]; exact phi_un h1 n1 n2
      · exact (phi_back (bi_keep hb hk3 n2 n4)).live hl2
lemma and_op (d : Bool) (a b n : ℕ) : op d a b &&& n = op d (a &&& n) (b &&& n) := by
  apply Nat.eq_of_testBit_eq; intro i
  cases d <;> simp [op_bit] <;> grind
lemma and_neg {m n : ℕ} (hn : n &&& m = n) (a : ℕ) : (a ^^^ m) &&& n = (a &&& n) ^^^ n := by
  apply Nat.eq_of_testBit_eq; intro i
  have := congrArg (fun x => x.testBit i) hn
  simp at this ⊢
  grind
abbrev Cst (n x : ℕ) : Prop := x &&& n = 0 ∨ x &&& n = n
def Im (n : ℕ) (S : Finset ℕ) : Set ℕ := (fun x => x &&& n) '' (S : Set ℕ)
lemma Im_mem {n x : ℕ} {S : Finset ℕ} (h : x ∈ S) : x &&& n ∈ C n (Im n S) := Or.inl ⟨x, by simpa using h, rfl⟩
lemma Cst_mem {n x : ℕ} {S : Set ℕ} (h : Cst n x) : x &&& n ∈ C n S := by
  rcases h with h | h <;> simp [C, h]
lemma Cst_neg {m n a : ℕ} (hn : n &&& m = n) : Cst n (a ^^^ m) ↔ Cst n a := by
  unfold Cst; rw [and_neg hn]
  constructor
  · rintro (h | h)
    · right; have := congrArg (· ^^^ n) h; simpa using this
    · left; have := congrArg (· ^^^ n) h; simpa using this
  · rintro (h | h) <;> simp [h]
lemma op_cst {n a b : ℕ} (d : Bool) (ha : Cst n a) :
    op d a b &&& n = 0 ∨ op d a b &&& n = n ∨ op d a b &&& n = b &&& n := by
  rw [and_op]
  rcases ha with h | h <;> rw [h] <;> cases d
  · left; simp [op]
  · right; right; simp [op]
  · right; right; apply Nat.eq_of_testBit_eq; intro i; simp [op]
  · right; left; apply Nat.eq_of_testBit_eq; intro i; simp [op]
lemma op_cst2 {n a b : ℕ} (d : Bool) (ha : Cst n a) (hb : Cst n b) : Cst n (op d a b) := by
  rcases op_cst (b := b) d ha with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · unfold Cst at hb ⊢; rw [h]; exact hb
lemma op_cst_mem {n a b : ℕ} {S : Finset ℕ} (d : Bool) (h : Cst n a ∨ Cst n b) (ha : a ∈ S) (hb : b ∈ S) :
    op d a b &&& n ∈ C n (Im n S) := by
  rcases h with h | h
  · rcases op_cst (b := b) d h with e | e | e <;> rw [e]
    · simp [C]
    · simp [C]
    · exact Im_mem hb
  · rw [op_comm]
    rcases op_cst (b := a) d h with e | e | e <;> rw [e]
    · simp [C]
    · simp [C]
    · exact Im_mem ha
lemma C_Im_sub {n g : ℕ} {S S' : Finset ℕ} {Q : Set ℕ} (h : S' ⊆ insert g S) (hg : g &&& n ∈ Q)
    (hQ : C n (Im n S) ⊆ Q) : C n (Im n S') ⊆ Q := by
  rintro x (⟨y, hy, rfl⟩ | hx)
  · have := h hy; simp at this
    rcases this with rfl | h'
    · exact hg
    · exact hQ (Im_mem h')
  · exact hQ (Or.inr hx)
section proj
variable {m T n : ℕ} (hn : n &&& m = n)
include hn
lemma Un.im {a q : ℕ} {S S' : Finset ℕ} (h : Un m a S S') (hs : Sol Z0 n (T &&& n) q (C n (Im n S'))) :
    Sol Z0 n (T &&& n) (q + 1) (C n (Im n S)) := by
  obtain ⟨ha, hsub⟩ := h.sub
  refine .un (Im_mem ha) (hs.mono le_rfl (C_Im_sub hsub ?_ (Set.subset_insert _ _)))
  rw [and_neg hn]; exact Or.inl rfl
omit hn in
lemma Bi.im {a b q : ℕ} {d : Bool} {S S' : Finset ℕ} (h : Bi R d a b S S') (hs : Sol Z0 n (T &&& n) q (C n (Im n S'))) :
    Sol Z0 n (T &&& n) (q + 1) (C n (Im n S)) := by
  obtain ⟨ha, hb, hsub⟩ := h.sub
  refine .bi (d := d) (Im_mem ha) (Im_mem hb) (al0 _ _ _) (hs.mono le_rfl (C_Im_sub hsub ?_ (Set.subset_insert _ _)))
  rw [and_op]; exact Or.inl rfl
lemma Un.kill {a q : ℕ} {S S' : Finset ℕ} (h : Un m a S S') (hc : Cst n a) (hs : Sol Z0 n (T &&& n) q (C n (Im n S'))) :
    Sol Z0 n (T &&& n) q (C n (Im n S)) :=
  hs.mono le_rfl (C_Im_sub h.sub.2 (Cst_mem ((Cst_neg hn).2 hc)) subset_rfl)
omit hn in
lemma Bi.kill {a b q : ℕ} {d : Bool} {S S' : Finset ℕ} (h : Bi R d a b S S') (hc : Cst n a ∨ Cst n b)
    (hs : Sol Z0 n (T &&& n) q (C n (Im n S'))) : Sol Z0 n (T &&& n) q (C n (Im n S)) :=
  hs.mono le_rfl (C_Im_sub h.sub.2.2 (op_cst_mem d hc h.sub.1 h.sub.2.1) subset_rfl)
lemma Min.const (hT0 : T &&& n ≠ 0) (hT1 : T &&& n ≠ n) {k t : ℕ} {S : Finset ℕ} (h : Min R m T k t S) :
    ∃ q, q + (S.filter (Cst n)).card ≤ k ∧ Sol Z0 n (T &&& n) q (C n (Im n S)) := by
  obtain ⟨hl, hm⟩ := h
  induction hl with
  | stop =>
    refine ⟨0, ?_, .done (Im_mem (by simp))⟩
    rw [Finset.filter_eq_empty_iff.2]; · simp
    intro x hx; simp at hx; subst hx
    rintro (h | h); exacts [hT0 h, hT1 h]
  | @un k t a U hl ih =>
    have hu : Un m a (insert a U) (insert (a ^^^ m) U) := ⟨U, rfl, rfl⟩
    obtain ⟨q, hq, hs⟩ := ih (hu.min hl hm).2
    have h1 : (U.filter (Cst n)).card ≤ ((insert (a ^^^ m) U).filter (Cst n)).card :=
      Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_insert _ _))
    by_cases hc : Cst n a
    · refine ⟨q, ?_, hu.kill hn hc hs⟩
      rw [Finset.filter_insert, ite_eq_left hc]
      have := Finset.card_insert_le a (U.filter (Cst n)); omega
    · refine ⟨q + 1, ?_, hu.im hn hs⟩
      rw [Finset.filter_insert, ite_eq_right hc]; omega
  | @bi k t d a b U hab hal hl ih =>
    have hu : Bi R d a b (insert a (insert b U)) (insert (op d a b) U) := ⟨hab, U, rfl, rfl, hal⟩
    obtain ⟨q, hq, hs⟩ := ih (hu.min hl hm).2
    have hf : op d a b ∉ U := fun h => hu.fresh hl hm (sub_C _ _ (by simp [h]))
    have h1 : (U.filter (Cst n)).card ≤ ((insert (op d a b) U).filter (Cst n)).card :=
      Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_insert _ _))
    have ca := Finset.card_insert_le a (U.filter (Cst n))
    have cb := Finset.card_insert_le b (U.filter (Cst n))
    by_cases hca : Cst n a
    · refine ⟨q, ?_, hu.kill (Or.inl hca) hs⟩
      rw [Finset.filter_insert, ite_eq_left hca, Finset.filter_insert]
      by_cases hcb : Cst n b
      · rw [ite_eq_left hcb]
        rw [Finset.filter_insert, ite_eq_left (op_cst2 d hca hcb), Finset.card_insert_of_notMem (by simp [hf])] at hq
        have := Finset.card_insert_le a (insert b (U.filter (Cst n))); omega
      · rw [ite_eq_right hcb]; omega
    · rw [Finset.filter_insert, ite_eq_right hca, Finset.filter_insert]
      by_cases hcb : Cst n b
      · refine ⟨q, ?_, hu.kill (Or.inr hcb) hs⟩
        rw [ite_eq_left hcb]; omega
      · refine ⟨q + 1, ?_, hu.im hs⟩
        rw [ite_eq_right hcb]; omega
end proj
lemma Min.proper {m T k t : ℕ} (hT : T &&& m = T) (hT0 : T ≠ 0) (hT1 : T ≠ m) {S : Finset ℕ} (hS : ∀ x ∈ S, x &&& m = x)
    (h : Min R m T k t S) : 0 ∉ S ∧ m ∉ S := by
  obtain ⟨q, hq, hs⟩ := h.const (n := m) (by simp) (by rwa [hT]) (by rwa [hT])
  have hi : Im m S = (S : Set ℕ) := by
    ext x; constructor
    · rintro ⟨y, hy, rfl⟩; have := hS y hy; simp only; rw [this]; exact hy
    · intro hx; exact ⟨x, hx, hS x hx⟩
  rw [hi, hT] at hs
  have key : ∀ x ∈ S, ¬ Cst m x := by
    intro x hx hc
    have : 0 < (S.filter (Cst m)).card := Finset.card_pos.2 ⟨x, by simp [hx, hc]⟩
    exact h.2 q (by omega) hs
  exact ⟨fun h0 => key 0 h0 (Or.inl (by simp)), fun h1 => key m h1 (Or.inr (by simp))⟩
def sepb (N : ℕ) (d : Bool) (w i : ℕ) : Bool :=
  bif d then xor (w.testBit i) (w.testBit (N + i)) else w.testBit i && !w.testBit (N + i)
def pos' (t : ℕ) : Bool := decide (0 < t)
section cov
variable {N m T i : ℕ} (m1 : m.testBit i = true) (m2 : m.testBit (N + i) = true)
  (t1 : T.testBit i = true) (t2 : T.testBit (N + i) = false)
include t1 t2 m1 m2
lemma Live.cov {k t : ℕ} {S : Finset ℕ} (h : Live R m T k t S) : ∃ w ∈ S, sepb N (pos' t) w i = true := by
  induction h with
  | stop => exact ⟨T, by simp, by simp [sepb, pos', t1, t2]⟩
  | @un k t a U _ ih =>
    obtain ⟨w, hw, hs⟩ := ih
    have weak : sepb N true w i = true := by
      revert hs; cases pos' t <;> simp [sepb] <;> cases w.testBit i <;> cases w.testBit (N + i) <;> simp
    simp at hw
    rcases hw with rfl | hw
    · refine ⟨a, by simp, ?_⟩
      revert weak; simp [sepb, pos', m1, m2]
    · exact ⟨w, by simp [hw], by simpa [pos'] using weak⟩
  | @bi k t d a b U _ _ _ ih =>
    obtain ⟨w, hw, hs⟩ := ih
    simp at hw
    rcases hw with rfl | hw
    · by_cases ha : sepb N (pos' t) a i = true
      · exact ⟨a, by simp, ha⟩
      · refine ⟨b, by simp, ?_⟩
        revert hs ha
        unfold sepb; simp only [op_bit]
        cases pos' t <;> cases d <;> cases a.testBit i <;> cases a.testBit (N + i) <;> cases b.testBit i <;>
          cases b.testBit (N + i) <;> simp
    · exact ⟨w, by simp [hw], hs⟩
end cov
def Uq (N : ℕ) (e : Bool) (S : Finset ℕ) (a i : ℕ) : Prop :=
  sepb N e a i = true ∧ ∀ c ∈ S, c ≠ a → sepb N e c i = false
lemma sepb_weak {N w i : ℕ} (e : Bool) (h : sepb N e w i = true) : sepb N true w i = true := by
  revert h; cases e <;> simp [sepb] <;> cases w.testBit i <;> cases w.testBit (N + i) <;> simp
section rect
variable {N m T : ℕ}
def Lg (N m T i : ℕ) : Prop := m.testBit i = true ∧ m.testBit (N + i) = true ∧ T.testBit i = true ∧ T.testBit (N + i) = false
lemma bi_uq {a b k t c i : ℕ} {d e : Bool} {U : Finset ℕ} (he : e = true ∨ e = pos' t) (hl : Live R m T k t (insert (op d a b) U))
    (ha : a ∉ U) (hb : b ∉ U) (hi : Lg N m T i)
    (hc : c ∈ insert a (insert b U)) (h : Uq N e (insert a (insert b U)) c i) :
    Uq N e (insert (op d a b) U) (if c = a ∨ c = b then op d a b else c) i := by
  obtain ⟨w, hw, hs⟩ := hl.cov hi.1 hi.2.1 hi.2.2.1 hi.2.2.2
  have hs : sepb N e w i = true := by
    rcases he with rfl | rfl
    · exact sepb_weak _ hs
    · exact hs
  by_cases hcc : c = a ∨ c = b
  · rw [ite_eq_left hcc]
    have hU : ∀ x ∈ U, sepb N e x i = false := by
      intro x hx
      refine h.2 x (by simp [hx]) ?_
      rintro rfl
      rcases hcc with rfl | rfl; exacts [ha hx, hb hx]
    simp at hw
    rcases hw with rfl | hw
    · refine ⟨hs, fun x hx hne => ?_⟩
      simp at hx; exact hU x (hx.resolve_left hne)
    · rw [hU w hw] at hs; simp at hs
  · rw [ite_eq_right hcc]
    push Not at hcc
    refine ⟨h.1, fun x hx hne => ?_⟩
    simp at hx
    rcases hx with rfl | hx
    · have h1 := h.2 a (by simp) (Ne.symm hcc.1)
      have h2 := h.2 b (by simp) (Ne.symm hcc.2)
      revert h1 h2; unfold sepb; simp only [op_bit]
      cases e <;> cases d <;> cases a.testBit i <;> cases a.testBit (N + i) <;> cases b.testBit i <;>
          cases b.testBit (N + i) <;> simp
    · exact h.2 x (by simp [hx]) hne
lemma un_uq {a c i : ℕ} {U : Finset ℕ} (hi : Lg N m T i) (ha : a ∉ U)
    (hc : c ∈ insert a U) (h : Uq N true (insert a U) c i) :
    Uq N true (insert (a ^^^ m) U) (if c = a then a ^^^ m else c) i := by
  have hn : sepb N true (a ^^^ m) i = sepb N true a i := by simp [sepb, hi.1, hi.2.1]
  by_cases hcc : c = a
  · rw [ite_eq_left hcc]; subst hcc
    refine ⟨by rw [hn]; exact h.1, fun x hx hne => ?_⟩
    simp at hx
    exact h.2 x (by simp [hx.resolve_left hne]) (fun e => ha (e ▸ hx.resolve_left hne))
  · rw [ite_eq_right hcc]
    refine ⟨h.1, fun x hx hne => ?_⟩
    simp at hx
    rcases hx with rfl | hx
    · rw [hn]; exact h.2 a (by simp) (Ne.symm hcc)
    · exact h.2 x (by simp [hx]) hne
lemma phi_mem {x y g c : ℕ} {U : Finset ℕ} (hc : c ∈ insert x (insert y U)) :
    (if c = x ∨ c = y then g else c) ∈ insert g U := by
  split_ifs with h
  · simp
  · simp only [Finset.mem_insert] at hc ⊢; tauto
lemma phi_ne {x y g a b : ℕ} {U : Finset ℕ} (hg : g ∉ U) (ha : a ∈ insert x (insert y U)) (hb : b ∈ insert x (insert y U))
    (hab : a ≠ b) (h : ¬ ((a = x ∨ a = y) ∧ (b = x ∨ b = y))) :
    (if a = x ∨ a = y then g else a) ≠ (if b = x ∨ b = y then g else b) := by
  simp only [Finset.mem_insert] at ha hb
  split_ifs with p q q
  · exact absurd ⟨p, q⟩ h
  · rintro rfl; tauto
  · rintro rfl; tauto
  · exact hab
lemma bi_tight {a b k t : ℕ} {d : Bool} {U : Finset ℕ} (hab : a ≠ b) (hal : Al R d a b) (hl : Live R m T k t (insert (op d a b) U))
    (hm : ∀ q < k + 1, ¬ Sol Z0 m T q (C m ((insert a (insert b U) : Finset ℕ) : Set ℕ)))
    (hc : (insert a (insert b U)).card + t = k + 2) :
    a ∉ U ∧ b ∉ U ∧ op d a b ∉ U ∧ (insert (op d a b) U).card + t = k + 1 ∧ Min R m T k t (insert (op d a b) U) := by
  have hu : Bi R d a b (insert a (insert b U)) (insert (op d a b) U) := ⟨hab, U, rfl, rfl, hal⟩
  have hf : op d a b ∉ U := fun h => hu.fresh hl hm (sub_C _ _ (by simp [h]))
  have hmin := hu.min hl hm
  have hs := hmin.size.1
  rw [Finset.card_insert_of_notMem hf] at hs ⊢
  have h1 := Finset.card_insert_le a (insert b U)
  have h2 := Finset.card_insert_le b U
  have ha : a ∉ insert b U := fun h => by rw [Finset.insert_eq_of_mem h] at hc; omega
  have hb : b ∉ U := fun h => by rw [Finset.insert_eq_of_mem h] at hc h1; omega
  exact ⟨fun h => ha (by simp [h]), hb, hf, by omega, hmin⟩
lemma un_tight {a k t : ℕ} {U : Finset ℕ} (hl : Live R m T k t (insert (a ^^^ m) U))
    (hm : ∀ q < k + 1, ¬ Sol Z0 m T q (C m ((insert a U : Finset ℕ) : Set ℕ)))
    (hc : (insert a U).card + (t + 1) = k + 2) :
    a ∉ U ∧ a ^^^ m ∉ U ∧ (insert (a ^^^ m) U).card + t = k + 1 ∧ Min R m T k t (insert (a ^^^ m) U) := by
  have hu : Un m a (insert a U) (insert (a ^^^ m) U) := ⟨U, rfl, rfl⟩
  have hf : a ^^^ m ∉ U := fun h => hu.fresh hl hm (sub_C _ _ (by simp [h]))
  have hmin := hu.min hl hm
  have hs := hmin.size.1
  rw [Finset.card_insert_of_notMem hf] at hs ⊢
  have h1 := Finset.card_insert_le a U
  have ha : a ∉ U := fun h => by rw [Finset.insert_eq_of_mem h] at hc; omega
  exact ⟨ha, hf, by omega, hmin⟩
lemma rect0 {k : ℕ} {S : Finset ℕ} (hl : Live R m T k 0 S) (hm : ∀ q < k, ¬ Sol Z0 m T q (C m (S : Set ℕ)))
    (hc : S.card = k + 1) {i1 i2 j1 j2 : ℕ} (h1 : Lg N m T i1) (h2 : Lg N m T i2) (h3 : Lg N m T j1) (h4 : Lg N m T j2) :
    ∀ {a b : ℕ}, a ∈ S → b ∈ S → a ≠ b →
    (∀ w ∈ S, w.testBit i1 = w.testBit i2) → (∀ w ∈ S, w.testBit (N + j1) = w.testBit (N + j2)) →
    Uq N false S a i1 → Uq N false S b i2 → Uq N false S a j1 → Uq N false S b j2 → False := by
  generalize ht : 0 = t at hl
  induction hl with
  | stop => intro a b ha hb hab; simp at ha hb; exact absurd (ha.trans hb.symm) hab
  | un => omega
  | @bi k t d x y U hxy hal hl ih =>
    subst ht
    intro a b ha hb hab r1 r2 u1 u2 u3 u4
    obtain ⟨hx, hy, hg, hc', hmin⟩ := bi_tight hxy hal hl hm (by simpa using hc)
    have tr : ∀ {c i}, Lg N m T i → c ∈ insert x (insert y U) → Uq N false (insert x (insert y U)) c i →
        Uq N false (insert (op d x y) U) (if c = x ∨ c = y then op d x y else c) i :=
      fun hi hc h => bi_uq (Or.inr (by simp [pos'])) hl hx hy hi hc h
    by_cases hab' : (a = x ∨ a = y) ∧ (b = x ∨ b = y)
    · have v1 := tr h1 ha u1; have v2 := tr h2 hb u2; have v3 := tr h3 ha u3; have v4 := tr h4 hb u4
      rw [ite_eq_left hab'.1] at v1 v3; rw [ite_eq_left hab'.2] at v2 v4
      have hop : op d x y = op d a b := by
        rcases hab' with ⟨rfl | rfl, rfl | rfl⟩
        · exact absurd rfl hab
        · rfl
        · exact op_comm _ _ _
        · exact absurd rfl hab
      rw [hop] at v1 v2 v3 v4
      have e1 := r1 b hb; have e2 := r2 b hb
      have n1 := u1.2 b hb (Ne.symm hab); have n3 := u3.2 b hb (Ne.symm hab)
      have s1 := v1.1; have s3 := v3.1; have s2 := u2.1; have s4 := u4.1
      revert e1 e2 n1 n3 s1 s3 s2 s4
      unfold sepb; simp only [op_bit]
      cases d <;> simp <;> grind
    · refine ih hmin.2 (by simpa using hc') rfl ?_ ?_ ?_ ?_ ?_ (tr h1 ha u1) (tr h2 hb u2) (tr h3 ha u3) (tr h4 hb u4)
      · exact phi_mem ha
      · exact phi_mem hb
      · exact phi_ne hg ha hb hab hab'
      · intro w hw; simp at hw
        rcases hw with rfl | hw
        · simp only [op_bit, r1 x (by simp), r1 y (by simp)]
        · exact r1 w (by simp [hw])
      · intro w hw; simp at hw
        rcases hw with rfl | hw
        · simp only [op_bit, r2 x (by simp), r2 y (by simp)]
        · exact r2 w (by simp [hw])
lemma polar {k t : ℕ} {S : Finset ℕ} (hl : Live R m T k t S) (hm : ∀ q < k, ¬ Sol Z0 m T q (C m (S : Set ℕ)))
    (hc : S.card + t = k + 1) {i j : ℕ} (h1 : Lg N m T i) (h2 : Lg N m T j) :
    ∀ {a : ℕ}, a ∈ S → Uq N true S a i → Uq N true S a j → a.testBit i = a.testBit j := by
  induction hl with
  | stop => intro a ha _ _; simp at ha; subst ha; rw [h1.2.2.1, h2.2.2.1]
  | @un k t x U hl ih =>
    intro a ha u1 u2
    obtain ⟨hx, hg, hc', hmin⟩ := un_tight hl hm (by omega)
    have := ih hmin.2 hc' (a := if a = x then x ^^^ m else a) (by split_ifs with h <;> simp at ha ⊢; tauto)
      (un_uq h1 hx ha u1) (un_uq h2 hx ha u2)
    split_ifs at this with h
    · subst h; simpa [h1.1, h2.1] using this
    · exact this
  | @bi k t d x y U hxy hal hl ih =>
    intro a ha u1 u2
    obtain ⟨hx, hy, hg, hc', hmin⟩ := bi_tight hxy hal hl hm (by omega)
    have v1 := bi_uq (Or.inl rfl) hl hx hy h1 ha u1
    have v2 := bi_uq (Or.inl rfl) hl hx hy h2 ha u2
    have := ih hmin.2 hc' (phi_mem ha) v1 v2
    split_ifs at this v1 v2 with h
    · obtain ⟨b, hb, hab, hop⟩ : ∃ b ∈ insert x (insert y U), b ≠ a ∧ op d x y = op d a b := by
        rcases h with rfl | rfl
        · exact ⟨y, by simp, Ne.symm hxy, rfl⟩
        · exact ⟨x, by simp, hxy, op_comm _ _ _⟩
      rw [hop] at this v1 v2
      have n1 := u1.2 b hb hab; have n2 := u2.2 b hb hab
      have s1 := v1.1; have s2 := v2.1; have p1 := u1.1; have p2 := u2.1
      revert this n1 n2 s1 s2 p1 p2
      unfold sepb; simp only [op_bit]
      cases d <;> simp <;> grind
    · exact this
lemma rect1 {k t : ℕ} {S : Finset ℕ} (hl : Live R m T k t S) (hm : ∀ q < k, ¬ Sol Z0 m T q (C m (S : Set ℕ)))
    (hc : S.card + t = k + 1) {i1 i2 j1 j2 : ℕ} (h1 : Lg N m T i1) (h2 : Lg N m T i2) (h3 : Lg N m T j1) (h4 : Lg N m T j2) :
    ∀ {a b : ℕ}, a ∈ S → b ∈ S → a ≠ b →
    (∀ w ∈ S, w.testBit i1 = w.testBit i2) → (∀ w ∈ S, w.testBit (N + j1) = w.testBit (N + j2)) →
    Uq N true S a i1 → Uq N true S b i2 → Uq N true S a j1 → Uq N true S b j2 → False := by
  induction hl with
  | stop => intro a b ha hb hab; simp at ha hb; exact absurd (ha.trans hb.symm) hab
  | @un k t x U hl ih =>
    intro a b ha hb hab r1 r2 u1 u2 u3 u4
    obtain ⟨hx, hg, hc', hmin⟩ := un_tight hl hm (by omega)
    refine ih hmin.2 hc' ?_ ?_ ?_ ?_ ?_ (un_uq h1 hx ha u1) (un_uq h2 hx hb u2) (un_uq h3 hx ha u3) (un_uq h4 hx hb u4)
    · split_ifs with h <;> simp at ha ⊢; tauto
    · split_ifs with h <;> simp at hb ⊢; tauto
    · split_ifs with p q q
      · exact absurd (p.trans q.symm) hab
      · intro e; simp at hb; rw [← e] at hb; rcases hb with h | h
        · exact q (by rw [← e, h])
        · exact hg h
      · intro e; simp at ha; rw [e] at ha; rcases ha with h | h
        · exact p (by rw [e, h])
        · exact hg h
      · exact hab
    · intro w hw; simp at hw
      rcases hw with rfl | hw
      · simp [r1 x (by simp), h1.1, h2.1]
      · exact r1 w (by simp [hw])
    · intro w hw; simp at hw
      rcases hw with rfl | hw
      · simp [r2 x (by simp), h3.2.1, h4.2.1]
      · exact r2 w (by simp [hw])
  | @bi k t d x y U hxy hal hl ih =>
    intro a b ha hb hab r1 r2 u1 u2 u3 u4
    obtain ⟨hx, hy, hg, hc', hmin⟩ := bi_tight hxy hal hl hm (by omega)
    have tr : ∀ {c i}, Lg N m T i → c ∈ insert x (insert y U) → Uq N true (insert x (insert y U)) c i →
        Uq N true (insert (op d x y) U) (if c = x ∨ c = y then op d x y else c) i :=
      fun hi hc h => bi_uq (Or.inl rfl) hl hx hy hi hc h
    by_cases hab' : (a = x ∨ a = y) ∧ (b = x ∨ b = y)
    · have v1 := tr h1 ha u1; have v2 := tr h2 hb u2; have v3 := tr h3 ha u3; have v4 := tr h4 hb u4
      rw [ite_eq_left hab'.1] at v1 v3; rw [ite_eq_left hab'.2] at v2 v4
      have hpol := polar hl hmin.2 hc' h1 h3 (by simp) v1 v3
      have hop : op d x y = op d a b := by
        rcases hab' with ⟨rfl | rfl, rfl | rfl⟩
        · exact absurd rfl hab
        · rfl
        · exact op_comm _ _ _
        · exact absurd rfl hab
      rw [hop] at v1 v2 v3 v4 hpol
      have e1 := r1 a ha; have e2 := r2 a ha; have e1b := r1 b hb; have e2b := r2 b hb
      have n1 := u1.2 b hb (Ne.symm hab); have n3 := u3.2 b hb (Ne.symm hab)
      have n2 := u2.2 a ha hab; have n4 := u4.2 a ha hab
      have s1 := v1.1; have s3 := v3.1; have s2 := v2.1; have s4 := v4.1
      have p1 := u1.1; have p2 := u2.1; have p3 := u3.1; have p4 := u4.1
      revert e1 e2 e1b e2b n1 n2 n3 n4 s1 s2 s3 s4 p1 p2 p3 p4 hpol
      unfold sepb; simp only [op_bit]
      cases d <;> simp <;> grind
    · refine ih hmin.2 hc' ?_ ?_ ?_ ?_ ?_ (tr h1 ha u1) (tr h2 hb u2) (tr h3 ha u3) (tr h4 hb u4)
      · exact phi_mem ha
      · exact phi_mem hb
      · exact phi_ne hg ha hb hab hab'
      · intro w hw; simp at hw
        rcases hw with rfl | hw
        · simp only [op_bit, r1 x (by simp), r1 y (by simp)]
        · exact r1 w (by simp [hw])
      · intro w hw; simp at hw
        rcases hw with rfl | hw
        · simp only [op_bit, r2 x (by simp), r2 y (by simp)]
        · exact r2 w (by simp [hw])
end rect
section chrom
variable {N m T : ℕ}
def Ht (N m T : ℕ) (e : Bool) (S : Finset ℕ) (a b : ℕ) : Prop := ∃ i1 i2 j1 j2, Lg N m T i1 ∧ Lg N m T i2 ∧ Lg N m T j1 ∧ Lg N m T j2 ∧
  (∀ w ∈ S, w.testBit i1 = w.testBit i2) ∧ (∀ w ∈ S, w.testBit (N + j1) = w.testBit (N + j2)) ∧
  Uq N e S a i1 ∧ Uq N e S b i2 ∧ Uq N e S a j1 ∧ Uq N e S b j2 ∧ a.testBit i1 = a.testBit j1 ∧ b.testBit i2 = b.testBit j2
lemma Ht.symm {e : Bool} {S : Finset ℕ} {a b : ℕ} (h : Ht N m T e S a b) : Ht N m T e S b a := by
  obtain ⟨i1, i2, j1, j2, l1, l2, l3, l4, r1, r2, u1, u2, u3, u4, p1, p2⟩ := h
  exact ⟨i2, i1, j2, j1, l2, l1, l4, l3, fun w hw => (r1 w hw).symm, fun w hw => (r2 w hw).symm, u2, u1, u4, u3, p2, p1⟩
lemma bi_uq2 {a b k t c i : ℕ} {d e : Bool} {U : Finset ℕ} (he : e = true ∨ e = pos' t) (hl : Live R m T k t (insert (op d a b) U))
    (hi : Lg N m T i) (hc : c ∈ insert a (insert b U)) (h1 : c = a → a ∉ U) (h2 : c = b → b ∉ U)
    (h : Uq N e (insert a (insert b U)) c i) :
    Uq N e (insert (op d a b) U) (if c = a ∨ c = b then op d a b else c) i := by
  obtain ⟨w, hw, hs⟩ := hl.cov hi.1 hi.2.1 hi.2.2.1 hi.2.2.2
  have hs : sepb N e w i = true := by
    rcases he with rfl | rfl
    · exact sepb_weak _ hs
    · exact hs
  by_cases hcc : c = a ∨ c = b
  · rw [ite_eq_left hcc]
    have hcU : c ∉ U := by
      rcases hcc with rfl | rfl; exacts [h1 rfl, h2 rfl]
    have hU : ∀ x ∈ U, sepb N e x i = false := by
      intro x hx
      refine h.2 x (by simp [hx]) ?_
      rintro rfl; exact hcU hx
    simp at hw
    rcases hw with rfl | hw
    · refine ⟨hs, fun x hx hne => ?_⟩
      simp at hx; exact hU x (hx.resolve_left hne)
    · rw [hU w hw] at hs; simp at hs
  · rw [ite_eq_right hcc]
    push Not at hcc
    refine ⟨h.1, fun x hx hne => ?_⟩
    simp at hx
    rcases hx with rfl | hx
    · have h1 := h.2 a (by simp) (Ne.symm hcc.1)
      have h2 := h.2 b (by simp) (Ne.symm hcc.2)
      revert h1 h2; unfold sepb; simp only [op_bit]
      cases e <;> cases d <;> cases a.testBit i <;> cases a.testBit (N + i) <;> cases b.testBit i <;>
          cases b.testBit (N + i) <;> simp
    · exact h.2 x (by simp [hx]) hne
lemma pol_op {a b i : ℕ} {d e : Bool} (ha : sepb N e a i = true) (hb : sepb N e b i = false) (ho : sepb N e (op d a b) i = true) :
    (op d a b).testBit i = a.testBit i := by
  revert ha hb ho; unfold sepb; simp only [op_bit]
  cases e <;> cases d <;> cases a.testBit i <;> cases a.testBit (N + i) <;> cases b.testBit i <;>
    cases b.testBit (N + i) <;> simp
lemma pol_phi {a b c i : ℕ} {d e : Bool} {U : Finset ℕ} (hab : a ≠ b) (h : Uq N e (insert a (insert b U)) c i)
    (hu : Uq N e (insert (op d a b) U) (if c = a ∨ c = b then op d a b else c) i) :
    (if c = a ∨ c = b then op d a b else c).testBit i = c.testBit i := by
  by_cases hcc : c = a ∨ c = b
  · rw [ite_eq_left hcc] at hu ⊢
    rcases hcc with rfl | rfl
    · exact pol_op h.1 (h.2 b (by simp) (Ne.symm hab)) hu.1
    · rw [op_comm] at hu ⊢
      exact pol_op h.1 (h.2 a (by simp) hab) hu.1
  · rw [ite_eq_right hcc]
lemma ht_bi {a b k t c1 c2 : ℕ} {d e : Bool} {U : Finset ℕ} (hab : a ≠ b) (he : e = true ∨ e = pos' t) (hl : Live R m T k t (insert (op d a b) U))
    (hc1 : c1 ∈ insert a (insert b U)) (hc2 : c2 ∈ insert a (insert b U))
    (h1 : c1 = a → a ∉ U) (h1' : c1 = b → b ∉ U) (h2 : c2 = a → a ∉ U) (h2' : c2 = b → b ∉ U)
    (h : Ht N m T e (insert a (insert b U)) c1 c2) :
    Ht N m T e (insert (op d a b) U) (if c1 = a ∨ c1 = b then op d a b else c1) (if c2 = a ∨ c2 = b then op d a b else c2) := by
  obtain ⟨i1, i2, j1, j2, l1, l2, l3, l4, r1, r2, u1, u2, u3, u4, p1, p2⟩ := h
  have v1 := bi_uq2 he hl l1 hc1 h1 h1' u1
  have v2 := bi_uq2 he hl l2 hc2 h2 h2' u2
  have v3 := bi_uq2 he hl l3 hc1 h1 h1' u3
  have v4 := bi_uq2 he hl l4 hc2 h2 h2' u4
  refine ⟨i1, i2, j1, j2, l1, l2, l3, l4, ?_, ?_, v1, v2, v3, v4, ?_, ?_⟩
  · intro w hw; simp at hw
    rcases hw with rfl | hw
    · simp only [op_bit, r1 a (by simp), r1 b (by simp)]
    · exact r1 w (by simp [hw])
  · intro w hw; simp at hw
    rcases hw with rfl | hw
    · simp only [op_bit, r2 a (by simp), r2 b (by simp)]
    · exact r2 w (by simp [hw])
  · rw [pol_phi hab u1 v1, pol_phi hab u3 v3, p1]
  · rw [pol_phi hab u2 v2, pol_phi hab u4 v4, p2]
lemma ht_merge {a b k t : ℕ} {d e : Bool} {U : Finset ℕ} (hab : a ≠ b) (he : e = true ∨ e = pos' t) (hl : Live R m T k t (insert (op d a b) U))
    (ha : a ∉ U) (hb : b ∉ U) (h : Ht N m T e (insert a (insert b U)) a b) : False := by
  obtain ⟨i1, i2, j1, j2, l1, l2, l3, l4, r1, r2, u1, u2, u3, u4, p1, p2⟩ := h
  have v1 := (bi_uq2 he hl l1 (by simp) (fun _ => ha) (fun _ => hb) u1).1
  have v2 := (bi_uq2 he hl l2 (by simp) (fun _ => ha) (fun _ => hb) u2).1
  have v3 := (bi_uq2 he hl l3 (by simp) (fun _ => ha) (fun _ => hb) u3).1
  have v4 := (bi_uq2 he hl l4 (by simp) (fun _ => ha) (fun _ => hb) u4).1
  simp only [true_or, or_true, if_true] at v1 v2 v3 v4
  have e1 := r1 a (by simp); have e2 := r2 a (by simp); have e1b := r1 b (by simp); have e2b := r2 b (by simp)
  have n1 := u1.2 b (by simp) (Ne.symm hab); have n3 := u3.2 b (by simp) (Ne.symm hab)
  have n2 := u2.2 a (by simp) hab; have n4 := u4.2 a (by simp) hab
  have s1 := u1.1; have s2 := u2.1; have s3 := u3.1; have s4 := u4.1
  revert e1 e2 e1b e2b n1 n2 n3 n4 s1 s2 s3 s4 v1 v2 v3 v4 p1 p2
  unfold sepb; simp only [op_bit]
  cases e <;> cases d <;> simp <;> grind
lemma un_uq2 {a c i : ℕ} {U : Finset ℕ} (hi : Lg N m T i) (h1 : c = a → a ∉ U) (hc : c ∈ insert a U) (h : Uq N true (insert a U) c i) :
    Uq N true (insert (a ^^^ m) U) (if c = a then a ^^^ m else c) i := by
  by_cases hca : c = a
  · exact un_uq hi (h1 hca) hc h
  · rw [ite_eq_right hca]
    have hn : sepb N true (a ^^^ m) i = sepb N true a i := by simp [sepb, hi.1, hi.2.1]
    refine ⟨h.1, fun x hx hne => ?_⟩
    simp at hx
    rcases hx with rfl | hx
    · rw [hn]; exact h.2 a (by simp) (Ne.symm hca)
    · exact h.2 x (by simp [hx]) hne
lemma ht_un {a c1 c2 : ℕ} {U : Finset ℕ} (hc1 : c1 ∈ insert a U) (hc2 : c2 ∈ insert a U) (h1 : c1 = a → a ∉ U) (h2 : c2 = a → a ∉ U)
    (h : Ht N m T true (insert a U) c1 c2) :
    Ht N m T true (insert (a ^^^ m) U) (if c1 = a then a ^^^ m else c1) (if c2 = a then a ^^^ m else c2) := by
  obtain ⟨i1, i2, j1, j2, l1, l2, l3, l4, r1, r2, u1, u2, u3, u4, p1, p2⟩ := h
  have pp : ∀ {c i j : ℕ}, m.testBit i = true → m.testBit j = true → c.testBit i = c.testBit j →
      (if c = a then a ^^^ m else c).testBit i = (if c = a then a ^^^ m else c).testBit j := by
    intro c i j m1 m2 p
    split_ifs with h
    · subst h; simp [m1, m2, p]
    · exact p
  refine ⟨i1, i2, j1, j2, l1, l2, l3, l4, ?_, ?_, un_uq2 l1 h1 hc1 u1, un_uq2 l2 h2 hc2 u2, un_uq2 l3 h1 hc1 u3, un_uq2 l4 h2 hc2 u4,
    pp l1.1 l3.1 p1, pp l2.1 l4.1 p2⟩
  · intro w hw; simp at hw
    rcases hw with rfl | hw
    · simp [r1 a (by simp), l1.1, l2.1]
    · exact r1 w (by simp [hw])
  · intro w hw; simp at hw
    rcases hw with rfl | hw
    · simp [r2 a (by simp), l3.2.1, l4.2.1]
    · exact r2 w (by simp [hw])
lemma chrom {e : Bool} {k t : ℕ} {S : Finset ℕ} (hl : Live R m T k t S) (hm : ∀ q < k, ¬ Sol Z0 m T q (C m (S : Set ℕ)))
    (he : e = true ∨ t = 0) :
    ∃ (x : ℕ) (f : ℕ → ℕ), S.card + t + x = k + 1 ∧ (∀ a ∈ S, f a ≤ x) ∧ ∀ a ∈ S, ∀ b ∈ S, a ≠ b → Ht N m T e S a b → f a ≠ f b := by
  induction hl with
  | stop =>
    refine ⟨0, fun _ => 0, by simp, by simp, ?_⟩
    intro a ha b hb hab; simp at ha hb; exact absurd (ha.trans hb.symm) hab
  | @un k t a U hl ih =>
    have he1 : e = true := he.resolve_right (by omega)
    subst he1
    have hu : Un m a (insert a U) (insert (a ^^^ m) U) := ⟨U, rfl, rfl⟩
    have hf : a ^^^ m ∉ U := fun h => hu.fresh hl hm (sub_C _ _ (by simp [h]))
    have hmin := hu.min hl hm
    obtain ⟨x, f, hx, hfx, hc⟩ := ih hmin.2 (Or.inl rfl)
    rw [Finset.card_insert_of_notMem hf] at hx
    have sm : ∀ {i1 i2 : ℕ}, m.testBit i1 = true → m.testBit i2 = true → (∀ w ∈ insert a U, w.testBit i1 = w.testBit i2) →
        ∀ w ∈ insert (a ^^^ m) U, w.testBit i1 = w.testBit i2 := by
      intro i1 i2 m1 m2 r w hw
      simp at hw
      rcases hw with rfl | hw
      · simp [r a (by simp), m1, m2]
      · exact r w (by simp [hw])
    by_cases ha : a ∈ U
    · have eS : insert a U = U := Finset.insert_eq_of_mem ha
      refine ⟨x + 1, fun c => if c = a then x + 1 else f c, by rw [eS]; omega, ?_, ?_⟩
      · intro c hcS
        rw [eS] at hcS
        by_cases hca : c = a
        · simp [hca]
        · simp only [hca, if_false]
          have := hfx c (by simp [hcS]); omega
      · intro c1 h1 c2 h2 h12 hh
        rw [eS] at h1 h2
        by_cases q1 : c1 = a
        · have q2 : c2 ≠ a := fun e => h12 (q1.trans e.symm)
          have := hfx c2 (by simp [h2])
          simp only [q1, q2, if_true, if_false]; omega
        · by_cases q2 : c2 = a
          · have := hfx c1 (by simp [h1])
            simp only [q1, q2, if_true, if_false]; omega
          · simp only [q1, q2, if_false]
            refine hc c1 (by simp [h1]) c2 (by simp [h2]) h12 ?_
            obtain ⟨i1, i2, j1, j2, l1, l2, l3, l4, r1, r2, u1, u2, u3, u4, p1, p2⟩ := hh
            have tr : ∀ {c i : ℕ}, c ≠ a → Lg N m T i → Uq N true (insert a U) c i → Uq N true (insert (a ^^^ m) U) c i := by
              intro c i hca hi h
              refine ⟨h.1, fun y hy hne => ?_⟩
              simp at hy
              rcases hy with rfl | hy
              · have hn : sepb N true (a ^^^ m) i = sepb N true a i := by simp [sepb, hi.1, hi.2.1]
                rw [hn]; exact h.2 a (by simp) (Ne.symm hca)
              · exact h.2 y (by simp [hy]) hne
            exact ⟨i1, i2, j1, j2, l1, l2, l3, l4, sm l1.1 l2.1 r1, sm l3.2.1 l4.2.1 r2, tr q1 l1 u1, tr q2 l2 u2, tr q1 l3 u3, tr q2 l4 u4, p1, p2⟩
    · rw [Finset.card_insert_of_notMem ha]
      have mem : ∀ {c : ℕ}, c ∈ insert a U → (if c = a then a ^^^ m else c) ∈ insert (a ^^^ m) U := by
        intro c hcS; split_ifs with h <;> simp at hcS ⊢; tauto
      refine ⟨x, fun c => f (if c = a then a ^^^ m else c), by omega, fun c hcS => hfx _ (mem hcS), ?_⟩
      intro c1 h1 c2 h2 h12 hh
      refine hc _ (mem h1) _ (mem h2) ?_ ?_
      · split_ifs with p q q
        · exact absurd (p.trans q.symm) h12
        · intro e; simp at h2; rw [← e] at h2; rcases h2 with h | h
          · exact q (by rw [← e, h])
          · exact hf h
        · intro e; simp at h1; rw [e] at h1; rcases h1 with h | h
          · exact p (by rw [e, h])
          · exact hf h
        · exact h12
      · obtain ⟨i1, i2, j1, j2, l1, l2, l3, l4, r1, r2, u1, u2, u3, u4, p1, p2⟩ := hh
        have pp : ∀ {c i j : ℕ}, m.testBit i = true → m.testBit j = true → c.testBit i = c.testBit j →
            (if c = a then a ^^^ m else c).testBit i = (if c = a then a ^^^ m else c).testBit j := by
          intro c i j m1 m2 p
          split_ifs with h
          · subst h; simp [m1, m2, p]
          · exact p
        exact ⟨i1, i2, j1, j2, l1, l2, l3, l4, sm l1.1 l2.1 r1, sm l3.2.1 l4.2.1 r2, un_uq l1 ha h1 u1, un_uq l2 ha h2 u2, un_uq l3 ha h1 u3, un_uq l4 ha h2 u4,
          pp l1.1 l3.1 p1, pp l2.1 l4.1 p2⟩
  | @bi k t d a b U hab hal hl ih =>
    have hu : Bi R d a b (insert a (insert b U)) (insert (op d a b) U) := ⟨hab, U, rfl, rfl, hal⟩
    have hfS : op d a b ∉ insert a (insert b U) := fun h => hu.fresh hl hm (sub_C _ _ (by simpa using h))
    have hf : op d a b ∉ U := fun h => hfS (by simp [h])
    have hmin := hu.min hl hm
    have he2 : e = true ∨ e = pos' t := by
      rcases he with h | h
      · exact Or.inl h
      · subst h; cases e <;> simp [pos']
    obtain ⟨x, f, hx, hfx, hc⟩ := ih hmin.2 he
    rw [Finset.card_insert_of_notMem hf] at hx
    have mem : ∀ {c : ℕ}, c ∈ insert a (insert b U) → (if c = a ∨ c = b then op d a b else c) ∈ insert (op d a b) U := fun h => phi_mem h
    by_cases ha : a ∈ U
    · by_cases hb : b ∈ U
      · have eS : insert a (insert b U) = U := by rw [Finset.insert_eq_of_mem hb, Finset.insert_eq_of_mem ha]
        refine ⟨x + 2, fun c => if c = a then x + 2 else if c = b then x + 1 else f c, by rw [eS]; omega, ?_, ?_⟩
        · intro c hcS
          rw [eS] at hcS
          have := hfx c (by simp [hcS])
          dsimp only; split_ifs <;> omega
        · intro c1 h1 c2 h2 h12 hh
          have k1 := h1; have k2 := h2
          rw [eS] at h1 h2
          have f1 := hfx c1 (by simp [h1]); have f2 := hfx c2 (by simp [h2])
          by_cases q1 : c1 = a
          · have q2 : c2 ≠ a := fun e => h12 (q1.trans e.symm)
            simp only [q1, q2, if_true, if_false]; split_ifs <;> omega
          · by_cases q2 : c2 = a
            · simp only [q1, q2, if_true, if_false]; split_ifs <;> omega
            · by_cases q3 : c1 = b
              · have q4 : c2 ≠ b := fun e => h12 (q3.trans e.symm)
                simp only [q1, q2, q3, q4, if_true, if_false]; rw [if_neg (Ne.symm hab)]; omega
              · by_cases q4 : c2 = b
                · simp only [q1, q2, q3, q4, if_true, if_false]; rw [if_neg (Ne.symm hab)]; omega
                · simp only [q1, q2, q3, q4, if_false]
                  have := ht_bi hab he2 hl k1 k2 (fun e => absurd e q1) (fun e => absurd e q3) (fun e => absurd e q2) (fun e => absurd e q4) hh
                  simp only [q1, q2, q3, q4, or_self, if_false] at this
                  exact hc c1 (by simp [h1]) c2 (by simp [h2]) h12 this
      · have eS : insert a (insert b U) = insert b U := Finset.insert_eq_of_mem (by simp [ha])
        refine ⟨x + 1, fun c => if c = a then x + 1 else f (if c = a ∨ c = b then op d a b else c), ?_, ?_, ?_⟩
        · rw [eS, Finset.card_insert_of_notMem hb]; omega
        · intro c hcS
          have := hfx _ (mem hcS)
          dsimp only; by_cases hca : c = a
          · simp [hca]
          · simp only [hca, if_false, false_or] at this ⊢; omega
        · intro c1 h1 c2 h2 h12 hh
          have f1 := hfx _ (mem h1); have f2 := hfx _ (mem h2)
          by_cases q1 : c1 = a
          · have q2 : c2 ≠ a := fun e => h12 (q1.trans e.symm)
            simp only [q1, q2, if_true, if_false, false_or] at f2 ⊢; omega
          · by_cases q2 : c2 = a
            · simp only [q1, q2, if_true, if_false, false_or] at f1 ⊢; omega
            · have := ht_bi hab he2 hl h1 h2 (fun e => absurd e q1) (fun _ => hb) (fun e => absurd e q2) (fun _ => hb) hh
              simp only [q1, q2, if_false, false_or] at this f1 f2 ⊢
              refine hc _ (by simpa [q1] using mem h1) _ (by simpa [q2] using mem h2) ?_ this
              have h1' : c1 = b ∨ c1 ∈ U := by simp at h1; tauto
              have h2' : c2 = b ∨ c2 ∈ U := by simp at h2; tauto
              split_ifs with p q q
              · exact absurd (p.trans q.symm) h12
              · intro e; exact hf (e ▸ h2'.resolve_left q)
              · intro e; exact hf (e ▸ h1'.resolve_left p)
              · exact h12
    · by_cases hb : b ∈ U
      · have eS : insert a (insert b U) = insert a U := by rw [Finset.insert_eq_of_mem hb]
        refine ⟨x + 1, fun c => if c = b then x + 1 else f (if c = a ∨ c = b then op d a b else c), ?_, ?_, ?_⟩
        · rw [eS, Finset.card_insert_of_notMem ha]; omega
        · intro c hcS
          have := hfx _ (mem hcS)
          dsimp only; by_cases hca : c = b
          · simp [hca]
          · simp only [hca, if_false, or_false] at this ⊢; omega
        · intro c1 h1 c2 h2 h12 hh
          have f1 := hfx _ (mem h1); have f2 := hfx _ (mem h2)
          by_cases q1 : c1 = b
          · have q2 : c2 ≠ b := fun e => h12 (q1.trans e.symm)
            simp only [q1, q2, if_true, if_false, or_false] at f2 ⊢; omega
          · by_cases q2 : c2 = b
            · simp only [q1, q2, if_true, if_false, or_false] at f1 ⊢; omega
            · have := ht_bi hab he2 hl h1 h2 (fun _ => ha) (fun e => absurd e q1) (fun _ => ha) (fun e => absurd e q2) hh
              simp only [q1, q2, if_false, or_false] at this f1 f2 ⊢
              refine hc _ (by simpa [q1] using mem h1) _ (by simpa [q2] using mem h2) ?_ this
              have h1' : c1 = a ∨ c1 ∈ U := by simp at h1; tauto
              have h2' : c2 = a ∨ c2 ∈ U := by simp at h2; tauto
              split_ifs with p q q
              · exact absurd (p.trans q.symm) h12
              · intro e; exact hf (e ▸ h2'.resolve_left q)
              · intro e; exact hf (e ▸ h1'.resolve_left p)
              · exact h12
      · refine ⟨x, fun c => f (if c = a ∨ c = b then op d a b else c), ?_, fun c hcS => hfx _ (mem hcS), ?_⟩
        · rw [Finset.card_insert_of_notMem (by simp [hab, ha]), Finset.card_insert_of_notMem hb]; omega
        · intro c1 h1 c2 h2 h12 hh
          by_cases hab' : (c1 = a ∨ c1 = b) ∧ (c2 = a ∨ c2 = b)
          · exfalso
            have : Ht N m T e (insert a (insert b U)) a b := by
              rcases hab' with ⟨rfl | rfl, rfl | rfl⟩
              · exact absurd rfl h12
              · exact hh
              · exact hh.symm
              · exact absurd rfl h12
            exact ht_merge hab he2 hl ha hb this
          · exact hc _ (mem h1) _ (mem h2) (phi_ne hf h1 h2 h12 hab')
              (ht_bi hab he2 hl h1 h2 (fun _ => ha) (fun _ => hb) (fun _ => ha) (fun _ => hb) hh)
end chrom
structure W where
  s : Nat
  a : Nat
  b : Nat
  c : Nat
  r : Nat
structure X where
  w : W
  s : Nat
  q : Nat
  u : Nat
structure Cm where
  a : List Nat
  b : List Nat
def NN : Nat := 4512
def AA : Nat := 0x7fffffffdfffffffffdffffffff7fffffffff7fffffff7ffffffffefffffffffdfffffffff7fffffffbfffffffdfffffffffbfffffffbfffffffff7fffffff7ffffffffdfffffffffbffffffffbfffffffdfffffffefffffffffdfffffffdfffffffff7fffffff7ffffffffefffffffffbffffffff7fffffff7ffffffffefffffffefffffffffbfffffffff7ffffffff7fffffff7ffffffdffffffefffffffff7ffffffdffffffffefffffffff7fffffffbfffffffbffffffbffffffeffffffffefffffff7fffffffefffffffff7fffffff7ffffffdffffffffdffffffffeffffffffbffffffffdfffffffdfffffffefff7beeefbeff7bedf7bfbddfddfeefef7fbeefbfbfdf7dddf7fbbddbfbbddfbbdfbbf7f7fffffffffffffbfbbddfefbfbfbbbef7fbfdfbfddffbf6feeffddfffffffffffffeffbf7feff7fefdffbfbfffffffffffffdffbfffffffffffffdfddddfdff7dfdfdfdddf7ef7f7fdfdffbeefbdff6efbfb777dfdff7fffffffffffffbf7fbdffbfdeffdfdff7f7efeff7ffbff7fffffffffffffbfdffdffbfffffffffffffdfdfdf7f7bbfbff77f7fdf7eff7ef7ff7fbfbdffdffdfdfeffdfbfdffdfffffffffffffeff7feffeffffffffffffff7fbfdfdfbdffbdffbfefeff7ff7fbffdfbfbff7fffffffffffffbff7fffffffffffffbfeffbffbfeffeffeffffffffffffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
def HX : Nat := 0x8411104100841208404220220110108041104040208222080442240442204420440808000000000000040442201040404441080402040220040901100220000000000000100408010080102004040000000000000200400000000000002022220200820202022208108080202004110420091040488820200800000000000004080420040210020200808101008004008000000000000040200200400000000000002020208084404008808020810081080080404200200202010020402002000000000000010080100100000000000000804020204200420040101008008040020404008000000000000040080000000000000401004004010010010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
def HY : Nat := 0x800000002000000000200000000800000000080000000800000000100000000020000000008000000040000000200000000040000000400000000080000000800000000200000000040000000040000000200000001000000000200000002000000000800000008000000001000000000400000000800000008000000001000000010000000004000000000800000000800000008000000200000010000000008000000200000000100000000080000000400000004000000400000010000000010000000800000001000000000800000008000000200000000200000000100000000400000000200000002000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
noncomputable section core
def st (n : Nat) (f : Nat → Bool) : Bool := Nat.rec (motive := fun _ => Bool) (f 0) (fun m _ => f m) (Nat.succ n)
def sp (d : Bool) (l s : Nat) : Nat :=
  Nat.land (Nat.xor s (Nat.land (Nat.shiftRight s NN) l)) (Bool.rec (motive := fun _ => Nat) (Nat.land s l) l d)
def cov (d : Bool) (l : Nat) (v : List W) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun w _ ih => Nat.lor (sp d l w.s) ih) v
def twice (d : Bool) (l : Nat) (v : List W) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun w t ih => Nat.lor (Nat.land (sp d l w.s) (cov d l t)) ih) v
def hit (f e : Nat) : Bool := (Bool.rec (motive := fun _ => Bool) ((Bool.rec (motive := fun _ => Bool) (true) (false) (Nat.beq (Nat.land (Nat.land f e) HY) 0))) (false) (Nat.beq (Nat.land (Nat.land f e) HX) 0))
def hits (f : Nat) (m : List Nat) : Bool := (List.rec (motive := fun _ => Bool) (false) (fun e _ ih => (Bool.rec (motive := fun _ => Bool) (ih) (true) (hit f e))) (m))
def flag (d : Bool) (l o : Nat) (w : W) : Nat := Nat.add (Nat.land (sp d l w.s) o) AA
def rect (d : Bool) (l o : Nat) (v : List W) : List Nat → Bool :=
  List.rec (motive := fun _ => List Nat → Bool) (fun _ => false)
    (fun w _ ih m => (Bool.rec (motive := fun _ => Bool) (ih (flag d l o w :: m)) (true) (hits (flag d l o w) m))) v
def app (x y : List Nat) : List Nat := List.rec (motive := fun _ => List Nat) y (fun e _ ih => e :: ih) x
def join (k : List Cm → Bool) (f : Nat) (cs : List Cm) : List Nat → List Nat → List Cm → Bool :=
  List.rec (motive := fun _ => List Nat → List Nat → List Cm → Bool) (fun S O R => k (⟨S, O⟩ :: R))
    (fun c _ ih S O R => Bool.rec (motive := fun _ => Bool)
      (Bool.rec (motive := fun _ => Bool) (ih S O (c :: R)) (ih (app c.a S) (app c.b O) R) (hits f c.b))
      (Bool.rec (motive := fun _ => Bool) (ih (app c.b S) (app c.a O) R) true (hits f c.b)) (hits f c.a)) cs
def bip (l o : Nat) (v : List W) : List Cm → Bool :=
  List.rec (motive := fun _ => List Cm → Bool) (fun _ => false)
    (fun w _ ih cs => (fun f => join ih f cs [f] [] []) (flag false l o w)) v
def anyE (m : List Nat) : Bool := List.rec (motive := fun _ => Bool) false (fun f t ih => Bool.rec (motive := fun _ => Bool) ih true (hits f t)) m
def rmF (f : Nat) (m : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) [] (fun e t ih => Bool.rec (motive := fun _ => List Nat) (e :: ih) t (hit f e)) m
def star (m : List Nat) : Bool := List.rec (motive := fun _ => Bool) true (fun f t ih => Bool.rec (motive := fun _ => Bool) ih
  (Bool.rec (motive := fun _ => Bool) true (Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) true false (anyE (rmF f t))) false (hits f (rmF f t))) (anyE t)) (hits f t)) m
def flk (l o : Nat) (v : List W) : (List Nat → Bool) → Bool :=
  List.rec (motive := fun _ => (List Nat → Bool) → Bool) (fun k => k []) (fun w _ ih k => (fun f => ih (fun r => k (f :: r))) (flag false l o w)) v
def mkX (d : Bool) (l o : Nat) (v : List W) : List X :=
  List.rec (motive := fun _ => List X) [] (fun w _ ih => ⟨w, w.s, Nat.shiftRight w.s NN, Nat.land (sp d l w.s) o⟩ :: ih) v
def rm (x y : Nat) (v : List W) : (List W → Bool) → Bool :=
  List.rec (motive := fun _ => (List W → Bool) → Bool) (fun h => h []) (fun w _ ih h => Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) (ih (fun r => h (w :: r))) (ih h) (Nat.beq w.s y)) (ih h) (Nat.beq w.s x)) v
def ins (o : W) (v : List W) : (List W → Bool) → Bool :=
  List.rec (motive := fun _ => (List W → Bool) → Bool) (fun h => h [o]) (fun w t ih h => Bool.rec (motive := fun _ => Bool) (ih (fun r => h (w :: r))) (Bool.rec (motive := fun _ => Bool) (h (o :: w :: t)) false (Nat.beq o.s w.s)) (Nat.ble w.s o.s)) v
def child (f : Nat → List W → Bool) (g : Nat) (mk : (List W → Bool) → Bool) (z : Nat) : Bool :=
  Bool.rec (motive := fun _ => Bool) false (st z (fun z => mk (f z))) (Nat.beq (Nat.land z g) g)
def put (m s x y : Nat) (v : List W) (h : List W → Bool) : Bool :=
  (st (s) (fun s => (Bool.rec (motive := fun _ => Bool) ((Bool.rec (motive := fun _ => Bool) ((st (x) (fun x1 => (st (y) (fun y1 => (st (Nat.lor x y) (fun w => ins ⟨s, x1, y1, w, 0⟩ v h))))))) (false) (Nat.beq s m))) (false) (Nat.beq s 0))))
def kids (c : ((List W → Bool) → Bool) → Nat → Bool) (e n z x y a c' : Nat) (oa oc : Bool) (mk : (List W → Bool) → Bool) : Bool :=
  (Bool.rec (motive := fun _ => Bool) ((Bool.rec (motive := fun _ => Bool) ((Bool.rec (motive := fun _ => Bool) (false) (c mk (Nat.sub (Nat.sub z x) y)) (Nat.ble (Nat.succ (Nat.succ n)) e))) (true) ((Bool.rec (motive := fun _ => Bool) (false) ((Bool.rec (motive := fun _ => Bool) ((Bool.rec (motive := fun _ => Bool) (false) (c (fun h => mk (fun r => rm a a r h)) (Nat.sub z y)) (oa))) (true) ((Bool.rec (motive := fun _ => Bool) (false) (c (fun h => mk (fun r => rm c' c' r h)) (Nat.sub z x)) (oc))))) (Nat.ble (Nat.succ n) e))))) (true) ((Bool.rec (motive := fun _ => Bool) (false) ((Bool.rec (motive := fun _ => Bool) (false) (c (fun h => mk (fun r => rm a c' r h)) z) (oc))) (oa))))
def mid (f : Nat → List W → Bool) (m g e n z : Nat) (v : List W) (a c : W) (da dc s x y : Nat) : Bool :=
  (Bool.rec (motive := fun _ => Bool) (false) ((st (Nat.sub (Nat.add z (Nat.land a.c c.c)) (Nat.lor x y)) (fun z => kids (child f g) e n z a.c c.c a.s c.s (Nat.beq da 0) (Nat.beq dc 0) (put m s x y v)))) (Nat.beq (Nat.land (Nat.sub (Nat.add z (Nat.land a.c c.c)) (Nat.lor x y)) g) g))
def f0 (h : W → W → Nat → Nat → Nat → Nat → Nat → Bool) (a c : W) (da dc s x y : Nat) : Bool :=
  (Bool.rec (motive := fun _ => Bool) (false) (h a c da dc s x y) (Nat.beq (Nat.lor da dc) 0))
def f1 (h : W → W → Nat → Nat → Nat → Nat → Nat → Bool) (a c : W) (da dc s x y : Nat) : Bool :=
  (Bool.rec (motive := fun _ => Bool) (false) (h a c da dc s x y) (Nat.beq (Nat.mul da dc) 0))
def f2 (h : W → W → Nat → Nat → Nat → Nat → Nat → Bool) (a c : W) (da dc s x y : Nat) : Bool := h a c da dc s x y
def pair (h : W → W → Nat → Nat → Nat → Nat → Nat → Bool) (a c : X) : Bool :=
  X.rec (motive := fun _ => Bool) (fun a s q u => X.rec (motive := fun _ => Bool) (fun c s' q' u' => (Bool.rec (motive := fun _ => Bool) (h a c (Nat.land u q') (Nat.land u' q) (Nat.lor s s') (Nat.land a.a c.a) (Nat.lor a.b c.b)) (true) (h a c (Nat.xor (Nat.land u s') u) (Nat.xor (Nat.land u' s) u') (Nat.land s s') (Nat.lor a.a c.a) (Nat.land a.b c.b)))) c) a
def scan (p : X → Bool) (xs : List X) : Bool := (List.rec (motive := fun _ => Bool) (false) (fun c _ jh => (Bool.rec (motive := fun _ => Bool) (jh) (true) (p c))) (xs))
def pairs (h : X → X → Bool) (xs : List X) : Bool :=
  (List.rec (motive := fun _ => Bool) (false) (fun a r ih => (Bool.rec (motive := fun _ => Bool) (ih) (true) (scan (h a) r))) (xs))
def pairsP (q : Nat) (h : X → X → Bool) (xs : List X) : Bool :=
  scan (fun a => (Bool.rec (motive := fun _ => Bool) (false) (scan (fun c => (Bool.rec (motive := fun _ => Bool) (h a c) (false) (Nat.beq c.s q))) xs) (Nat.beq a.s q))) xs
def pairsQ (q q' : Nat) (h : X → X → Bool) (xs : List X) : Bool :=
  scan (fun a => (Bool.rec (motive := fun _ => Bool) (false) (scan (fun c => (Bool.rec (motive := fun _ => Bool) (false) (h a c) (Nat.beq c.s q'))) xs) (Nat.beq a.s q))) xs
def fr (xs : List X) : List X := List.rec (motive := fun _ => List X) [] (fun a _ ih => Bool.rec (motive := fun _ => List X) ih (a :: ih) (Nat.beq a.w.r 0)) xs
def fs (xs : List X) : List X := List.rec (motive := fun _ => List X) [] (fun a _ ih => Bool.rec (motive := fun _ => List X) (a :: ih) ih (Nat.beq a.w.r 0)) xs
def pairsN (h : X → X → Bool) (xs : List X) : Bool :=
  Bool.rec (motive := fun _ => Bool) (scan (fun a => scan (h a) (fs xs)) (fr xs)) true (pairs h (fr xs))
def pairsS (h : X → X → Bool) (xs : List X) : Bool := pairs h (fs xs)
def nots (f : Nat → Nat → List W → Bool) (m g e n z q : Nat) (v r : List W) : Bool :=
  (List.rec (motive := fun _ => Bool) (false) (fun a _ ih => (Bool.rec (motive := fun _ => Bool) (ih) (true) ((Bool.rec (motive := fun _ => Bool) ((st (Nat.xor a.s m) (fun s => (st (Nat.sub z a.c) (fun z => ins ⟨s, a.b, a.a, a.c, 0⟩ v (fun v => (Bool.rec (motive := fun _ => Bool) ((Bool.rec (motive := fun _ => Bool) (false) (child (f s) g (fun h => h v) (Nat.sub z a.c)) (Nat.ble (Nat.succ n) e))) (true) ((Bool.rec (motive := fun _ => Bool) (false) (child (f s) g (rm a.s a.s v) z) (Nat.ble n e)))))))))) (false) (Nat.beq (Nat.succ a.s) q))))) (r))
def pos (t : Nat) : Bool := Nat.rec (motive := fun _ => Bool) false (fun _ _ => true) t
def wst (d : Bool) (l : Nat) (v : List W) : Nat := Nat.xor l (twice d l v)
def node (f : Nat → List W → Bool) (d : Bool) (l m g e n z : Nat) (v : List W) (go : (X → X → Bool) → List X → Bool) : Bool :=
  (fun h => (fun xs => Bool.rec (motive := fun _ => Bool) (go (pair (f0 h)) xs)
    (Bool.rec (motive := fun _ => Bool) (go (pair (f1 h)) xs) (go (pair (f2 h)) xs) (Nat.ble (Nat.succ n) e)) (Nat.ble n e))
    (mkX d l (wst d l v) v))
  (mid f m g e (Nat.pred n) z v)
def prd (t : Nat) (h : Nat → Bool) : Bool := Nat.rec (motive := fun _ => Bool) false (fun s _ => h s) t
def cv (d : Bool) (l : Nat) (v : List W) (b : Bool) : Bool :=
  Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) false b (Nat.beq (cov d l v) l)) b d
def tst (d : Bool) (l e : Nat) (v : List W) (F : Nat → Bool) : Bool :=
  (fun n => Bool.rec (motive := fun _ => Bool)
    (Bool.rec (motive := fun _ => Bool) (F 0) (Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) (F 1) (F 0) (flk l (wst d l v) v star)) false (bip l (wst d l v) v []))
      (Nat.beq (Nat.succ n) e))
    (Bool.rec (motive := fun _ => Bool) (F 0) false (rect d l (wst d l v) v [])) (Nat.beq n e)) v.length
def mv (F : Nat → Nat → Nat → List W → Bool) (l m g k t z : Nat) (v : List W) (y : Nat) : Bool :=
  (fun n => Bool.rec (motive := fun _ => Bool) (prd t (fun s => nots (fun q z v => cv (pos s) l v (tst (pos s) l (Nat.sub k s) v (fun y =>
      Bool.rec (motive := fun _ => Bool) (prd s (fun s => nots (fun q' z v => cv (pos s) l v (tst (pos s) l (Nat.sub (Nat.sub k 1) s) v (fun y =>
          node (F (Nat.sub k 3) s) (pos s) l m g (Nat.sub (Nat.sub (Nat.sub k 2) s) y) v.length z v (pairsQ q q'))))
          m g (Nat.sub (Nat.sub (Nat.sub k 1) s) y) v.length z (Nat.succ q) v v)) true
        (node (F (Nat.sub k 2) s) (pos s) l m g (Nat.sub (Nat.sub (Nat.sub k 1) s) y) v.length z v (pairsP q)))))
      m g (Nat.sub (Nat.sub k s) y) n z 0 v v)) true
    (node (F (Nat.sub k 1) t) (pos t) l m g (Nat.sub (Nat.sub k t) y) n z v pairsN)) v.length
def look (l m g : Nat) (fuel : Nat) : Nat → Nat → Nat → List W → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → List W → Bool) (fun _ _ _ _ => true)
    (fun _ ih k t z v => Bool.rec (motive := fun _ => Bool) (tst (pos t) l (Nat.sub (Nat.succ k) t) v (fun y => mv ih l m g k t z v y)) true (Nat.ble v.length 1)) fuel
def look1 (l m g K : Nat) (fuel : Nat) : Nat → Nat → Nat → List W → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → List W → Bool) (fun _ _ _ _ => true)
    (fun _ ih k t z v => Bool.rec (motive := fun _ => Bool) (tst (pos t) l (Nat.sub (Nat.succ k) t) v (fun y =>
      Bool.rec (motive := fun _ => Bool) (mv (look l m g K) l m g k t z v y) true
        (node (ih (Nat.sub k 1) t) (pos t) l m g (Nat.sub (Nat.sub k t) y) v.length z v pairsS))) true (Nat.ble v.length 1)) fuel
end core
lemma bR (c e t : Bool) : (Bool.rec (motive := fun _ => Bool) e t c : Bool) = bif c then t else e := by cases c <;> rfl
lemma st_eq (n : ℕ) (f : ℕ → Bool) : st n f = f n := by cases n <;> rfl
lemma nl (a b : ℕ) : Nat.land a b = a &&& b := rfl
lemma no (a b : ℕ) : Nat.lor a b = a ||| b := rfl
lemma nx (a b : ℕ) : Nat.xor a b = a ^^^ b := rfl
lemma nsr (a b : ℕ) : Nat.shiftRight a b = a >>> b := rfl
lemma sp_bit (d : Bool) (l s i : ℕ) : (sp d l s).testBit i = (l.testBit i && sepb NN d s i) := by
  cases d <;> simp [sp, sepb, nl, nx, nsr, Nat.testBit_shiftRight] <;>
    cases l.testBit i <;> cases s.testBit i <;> cases s.testBit (NN + i) <;> rfl
lemma cov_bit (d : Bool) (l i : ℕ) (v : List W) : (cov d l v).testBit i = true ↔ ∃ w ∈ v, (sp d l w.s).testBit i = true := by
  induction v with
  | nil => simp [cov]
  | cons w v ih =>
    change (Nat.lor (sp d l w.s) (cov d l v)).testBit i = true ↔ _
    simp [no, ih]
lemma twice_bit (d : Bool) (l i : ℕ) (v : List W) (h : (twice d l v).testBit i = false) :
    v.Pairwise (fun w w' => ¬ ((sp d l w.s).testBit i = true ∧ (sp d l w'.s).testBit i = true)) := by
  induction v with
  | nil => simp
  | cons w v ih =>
    change (Nat.lor (Nat.land (sp d l w.s) (cov d l v)) (twice d l v)).testBit i = false at h
    simp only [no, nl, Nat.testBit_or, Nat.testBit_and, Bool.or_eq_false_iff] at h
    refine List.pairwise_cons.2 ⟨fun w' hw' ⟨h1, h2⟩ => ?_, ih h.2⟩
    have := (cov_bit d l i v).2 ⟨w', hw', h2⟩
    simp [h1, this] at h
def Rep (v : List W) (S : Finset ℕ) : Prop := (v.map W.s).Nodup ∧ (v.map W.s).toFinset = S
lemma Rep.mem {v : List W} {S : Finset ℕ} (h : Rep v S) {x : ℕ} : x ∈ S ↔ ∃ w ∈ v, w.s = x := by
  rw [← h.2]; simp
lemma Rep.inj {v : List W} {S : Finset ℕ} (h : Rep v S) {w w' : W} (hw : w ∈ v) (hw' : w' ∈ v) (e : w.s = w'.s) : w = w' :=
  List.inj_on_of_nodup_map h.1 hw hw' e
lemma Rep.card {v : List W} {S : Finset ℕ} (h : Rep v S) : S.card = v.length := by
  rw [← h.2, List.toFinset_card_of_nodup h.1, List.length_map]
lemma uq_of {d : Bool} {l i : ℕ} {v : List W} {S : Finset ℕ} (h : Rep v S) {w : W} (hw : w ∈ v)
    (hu : (Nat.land (sp d l w.s) (wst d l v)).testBit i = true) : l.testBit i = true ∧ Uq NN d S w.s i := by
  simp only [nl, wst, nx, Nat.testBit_and, Nat.testBit_xor, Bool.and_eq_true, sp_bit] at hu
  obtain ⟨⟨hl, hs⟩, ht⟩ := hu
  have ht : (twice d l v).testBit i = false := by simpa [hl] using ht
  refine ⟨hl, hs, fun c hc hne => ?_⟩
  obtain ⟨w', hw', rfl⟩ := h.mem.1 hc
  have hp := twice_bit d l i v ht
  haveI : Std.Symm (fun w w' : W => ¬ ((sp d l w.s).testBit i = true ∧ (sp d l w'.s).testBit i = true)) :=
    ⟨fun a b h h' => h h'.symm⟩
  have := hp.forall hw hw' (fun e => hne (by rw [e]))
  simp only [sp_bit, hl, hs, Bool.true_and, true_and] at this
  simpa using this
def segsX : List (ℕ × ℕ) := [(511, 568), (568, 580), (580, 592), (592, 602), (602, 614), (614, 624), (624, 634), (634, 691), (691, 702), (702, 759), (759, 770), (770, 778), (778, 785), (785, 798), (798, 807), (807, 819), (819, 828), (828, 836), (836, 846), (846, 857), (857, 862), (862, 873), (873, 878), (878, 885), (885, 893), (893, 902), (902, 911), (911, 968), (968, 980), (980, 991), (991, 1000), (1000, 1057), (1057, 1069), (1069, 1078), (1078, 1085), (1085, 1096), (1096, 1105), (1105, 1113), (1113, 1125), (1125, 1137), (1137, 1142), (1142, 1150), (1150, 1159), (1159, 1171), (1171, 1176), (1176, 1183), (1183, 1192), (1192, 1199), (1199, 1205), (1205, 1215), (1215, 1223), (1223, 1227), (1227, 1238), (1238, 1246), (1246, 1250), (1250, 1255), (1255, 1263), (1263, 1269), (1269, 1277), (1277, 1285), (1285, 1342), (1342, 1353), (1353, 1365), (1365, 1374), (1374, 1431), (1431, 1442), (1442, 1455), (1455, 1464), (1464, 1472), (1472, 1479), (1479, 1487), (1487, 1497), (1497, 1505), (1505, 1516), (1516, 1521), (1521, 1530), (1530, 1541), (1541, 1546), (1546, 1555), (1555, 1562), (1562, 1619), (1619, 1629), (1629, 1637), (1637, 1643), (1643, 1647), (1647, 1651), (1651, 1654), (1654, 1662), (1662, 1668), (1668, 1672), (1672, 1675), (1675, 1685), (1685, 1690), (1690, 1696), (1696, 1700), (1700, 1706), (1706, 1717), (1717, 1725), (1725, 1735), (1735, 1743), (1743, 1748), (1748, 1755), (1755, 1761), (1761, 1765), (1765, 1769), (1769, 1777), (1777, 1785), (1785, 1793), (1793, 1799), (1799, 1809), (1809, 1817), (1817, 1821), (1821, 1825), (1825, 1829), (1829, 1837), (1837, 1894), (1894, 1905), (1905, 1962), (1962, 1970), (1970, 1981), (1981, 1988), (1988, 1999), (1999, 2008), (2008, 2019), (2019, 2026), (2026, 2036), (2036, 2093), (2093, 2097), (2097, 2108), (2108, 2112), (2112, 2120), (2120, 2123), (2123, 2130), (2130, 2141), (2141, 2145), (2145, 2154), (2154, 2161), (2161, 2170), (2170, 2179), (2179, 2184), (2184, 2190), (2190, 2194), (2194, 2198), (2198, 2206), (2206, 2214), (2214, 2220), (2220, 2229), (2229, 2233), (2233, 2238), (2238, 2242), (2242, 2250), (2250, 2307), (2307, 2315), (2315, 2322), (2322, 2326), (2326, 2333), (2333, 2338), (2338, 2342), (2342, 2349), (2349, 2353), (2353, 2358), (2358, 2362), (2362, 2370), (2370, 2373), (2373, 2377), (2377, 2382), (2382, 2386), (2386, 2395), (2395, 2401), (2401, 2405), (2405, 2409), (2409, 2415), (2415, 2421), (2421, 2430), (2430, 2438), (2438, 2444), (2444, 2448), (2448, 2454), (2454, 2463), (2463, 2468), (2468, 2476), (2476, 2480), (2480, 2489), (2489, 2493), (2493, 2501), (2501, 2505), (2505, 2510), (2510, 2518), (2518, 2523), (2523, 2529), (2529, 2532), (2532, 2538), (2538, 2543), (2543, 2552), (2552, 2558), (2558, 2564), (2564, 2568), (2568, 2572), (2572, 2578), (2578, 2583)]
def segsY : List (ℕ × ℕ) := [(2583, 2596), (2596, 2629), (2629, 2661), (2661, 2698), (2698, 2732), (2732, 2769), (2769, 2805), (2805, 2835), (2835, 2867), (2867, 2904), (2904, 2939), (2939, 2968), (2968, 3004), (3004, 3034), (3034, 3062), (3062, 3094), (3094, 3127), (3127, 3164), (3164, 3201), (3201, 3231), (3231, 3268), (3268, 3297), (3297, 3327), (3327, 3359), (3359, 3395), (3395, 3434), (3434, 3472), (3472, 3504), (3504, 3543), (3543, 3575), (3575, 3610), (3610, 3648), (3648, 3687), (3687, 3719), (3719, 3757), (3757, 3789), (3789, 3828), (3828, 3861), (3861, 3894), (3894, 3930), (3930, 3969), (3969, 4007), (4007, 4039), (4039, 4078), (4078, 4110), (4110, 4149), (4149, 4182), (4182, 4215), (4215, 4253), (4253, 4292), (4292, 4331), (4331, 4363), (4363, 4403), (4403, 4437), (4437, 4477), (4477, 4511)]
def segOk (s : ℕ × ℕ) : Bool := decide (s.1 < s.2) && decide (AA % 2 ^ s.2 + 2 ^ (s.1 + 1) = 2 ^ s.2 + AA % 2 ^ s.1) &&
  !AA.testBit s.1 && !AA.testBit s.2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma segX_ok : segsX.all segOk = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma segY_ok : segsY.all segOk = true := by decide +kernel
def bitsOf (L : List (ℕ × ℕ)) : ℕ := L.foldr (fun s x => 2 ^ s.2 ||| x) 0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma HX_eq : HX = bitsOf segsX := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma HY_eq : HY = bitsOf segsY := by decide +kernel
lemma bitsOf_bit {L : List (ℕ × ℕ)} {h : ℕ} (hh : (bitsOf L).testBit h = true) : ∃ s ∈ L, s.2 = h := by
  induction L with
  | nil => simp [bitsOf] at hh
  | cons s L ih =>
    change (2 ^ s.2 ||| bitsOf L).testBit h = true at hh
    rw [Nat.testBit_or, Nat.testBit_two_pow, Bool.or_eq_true] at hh
    rcases hh with hh | hh
    · exact ⟨s, by simp, by simpa using hh⟩
    · obtain ⟨s', hs', e⟩ := ih hh; exact ⟨s', by simp [hs'], e⟩
lemma carry {u A p h : ℕ} (hp : p < h) (hA : A % 2 ^ h + 2 ^ (p + 1) = 2 ^ h + A % 2 ^ p) (hAh : A.testBit h = false)
    (huh : u.testBit h = false) (hup : u.testBit p = false) (hs : (u + A).testBit h = true) :
    ∃ i, p < i ∧ i < h ∧ u.testBit i = true := by
  by_contra hno
  push Not at hno
  have e1 : u % 2 ^ h = u % 2 ^ p := by
    apply Nat.eq_of_testBit_eq; intro i
    simp only [Nat.testBit_mod_two_pow]
    by_cases h1 : i < p
    · simp [h1, show i < h by omega]
    · by_cases h2 : i < h
      · rcases Nat.lt_or_ge p i with h3 | h3
        · simp [h1, hno i h3 h2]
        · obtain rfl : i = p := by omega
          simp [hup]
      · simp [h1, h2]
  have l1 := Nat.mod_lt u (Nat.two_pow_pos p)
  have l2 := Nat.mod_lt A (Nat.two_pow_pos p)
  have hlt : u % 2 ^ h + A % 2 ^ h < 2 ^ h := by rw [e1]; have := Nat.pow_succ 2 p; omega
  have e2 : (u + A).testBit h = (u / 2 ^ h + A / 2 ^ h).testBit 0 := by
    have : u + A = 2 ^ h * (u / 2 ^ h + A / 2 ^ h) + (u % 2 ^ h + A % 2 ^ h) := by
      have a1 := Nat.div_add_mod u (2 ^ h); have a2 := Nat.div_add_mod A (2 ^ h)
      rw [Nat.mul_add]; omega
    rw [this, Nat.testBit_two_pow_mul_add _ hlt]; simp
  have b1 : (u / 2 ^ h).testBit 0 = false := by rw [← huh, Nat.testBit_div_two_pow]; simp
  have b2 : (A / 2 ^ h).testBit 0 = false := by rw [← hAh, Nat.testBit_div_two_pow]; simp
  rw [e2] at hs
  simp [Nat.testBit_zero] at hs b1 b2
  omega
def Same (L : List (ℕ × ℕ)) (i j : ℕ) : Prop := ∃ s ∈ L, s.1 < i ∧ i < s.2 ∧ s.1 < j ∧ j < s.2
def Good (l s : ℕ) : Prop := (∀ i j, Same segsX i j → l.testBit i = true → l.testBit j = true → s.testBit i = s.testBit j) ∧
  (∀ i j, Same segsY i j → l.testBit i = true → l.testBit j = true → s.testBit (NN + i) = s.testBit (NN + j))
lemma flag_seg {L : List (ℕ × ℕ)} (hL : L.all segOk = true) {u : ℕ} (hu : ∀ i, u.testBit i = true → AA.testBit i = true)
    {s : ℕ × ℕ} (hs : s ∈ L) (hb : (u + AA).testBit s.2 = true) : ∃ i, s.1 < i ∧ i < s.2 ∧ u.testBit i = true := by
  have h := List.all_eq_true.1 hL s hs
  simp only [segOk, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h
  refine carry h.1.1.1 h.1.1.2 h.2 ?_ ?_ hb
  · by_contra hc; have := hu _ (by simpa using hc); rw [h.2] at this; simp at this
  · by_contra hc; have := hu _ (by simpa using hc); rw [h.1.2] at this; simp at this
lemma hit_spec {f e : ℕ} (h : hit f e = true) :
    (∃ s ∈ segsX, f.testBit s.2 = true ∧ e.testBit s.2 = true) ∧ (∃ s ∈ segsY, f.testBit s.2 = true ∧ e.testBit s.2 = true) := by
  have aux : ∀ H, Nat.beq (Nat.land (Nat.land f e) H) 0 = false → ∃ i, f.testBit i = true ∧ e.testBit i = true ∧ H.testBit i = true := by
    intro H hH
    have hne : (f &&& e &&& H) ≠ 0 := fun h0 => by rw [nl, nl, h0] at hH; simp at hH
    obtain ⟨i, hi⟩ := Nat.exists_testBit_of_ne_zero hne
    simp at hi; exact ⟨i, hi.1.1, hi.1.2, hi.2⟩
  simp only [hit, bR] at h
  cases h1 : Nat.beq (Nat.land (Nat.land f e) HX) 0 with
  | true => rw [h1] at h; simp only [cond_true, Bool.false_eq_true] at h
  | false =>
    cases h2 : Nat.beq (Nat.land (Nat.land f e) HY) 0 with
    | true => rw [h1, h2] at h; simp only [cond_true, cond_false, Bool.false_eq_true] at h
    | false =>
      obtain ⟨i, a1, a2, a3⟩ := aux _ h1
      obtain ⟨j, b1, b2, b3⟩ := aux _ h2
      rw [HX_eq] at a3; rw [HY_eq] at b3
      obtain ⟨s, hs, rfl⟩ := bitsOf_bit a3
      obtain ⟨s', hs', rfl⟩ := bitsOf_bit b3
      exact ⟨⟨s, hs, a1, a2⟩, ⟨s', hs', b1, b2⟩⟩
lemma hits_false {f : ℕ} {m : List ℕ} (h : ∀ e ∈ m, hit f e = false) : hits f m = false := by
  induction m with
  | nil => rfl
  | cons e m ih =>
    change (Bool.rec (motive := fun _ => Bool) (hits f m) true (hit f e) : Bool) = false
    rw [bR, h e (by simp), ih (fun x hx => h x (by simp [hx]))]; rfl
lemma rect_false {d : Bool} {l o : ℕ} {v : List W} : ∀ {m : List ℕ}, v.Pairwise (fun a b => hit (flag d l o b) (flag d l o a) = false) →
    (∀ w ∈ v, ∀ e ∈ m, hit (flag d l o w) e = false) → rect d l o v m = false := by
  induction v with
  | nil => intros; rfl
  | cons w v ih =>
    intro m hp hm
    change (Bool.rec (motive := fun _ => Bool) (rect d l o v (flag d l o w :: m)) true (hits (flag d l o w) m) : Bool) = false
    rw [List.pairwise_cons] at hp
    rw [bR, hits_false (hm w (by simp)), ih hp.2]; · rfl
    intro w' hw' e he
    simp at he
    rcases he with rfl | he
    · exact hp.1 w' hw'
    · exact hm w' (by simp [hw']) e he
lemma Live.pos {m T k t : ℕ} {S : Finset ℕ} (h : Live R m T k t S) : 0 < S.card := by
  cases h with
  | stop => simp
  | un => exact Finset.card_pos.2 (Finset.insert_nonempty _ _)
  | bi => exact Finset.card_pos.2 (Finset.insert_nonempty _ _)
def pk (n : ℕ) (f : ℕ → ℕ) : ℕ := ∑ j ∈ Finset.range n, f j * 2 ^ (5 * j)
lemma pk_succ (n : ℕ) (f : ℕ → ℕ) : pk (n + 1) f = 2 ^ (5 * n) * f n + pk n f := by
  rw [pk, Finset.sum_range_succ, ← pk]; ring
lemma pk_lt {n : ℕ} {f : ℕ → ℕ} (h : ∀ j < n, f j < 32) : pk n f < 2 ^ (5 * n) := by
  induction n with
  | zero => simp [pk]
  | succ n ih =>
    have := ih (fun j hj => h j (by omega))
    have h2 := h n (by omega)
    rw [pk_succ, show 5 * (n + 1) = 5 * n + 5 by ring, pow_add]
    have : 2 ^ (5 * n) * f n ≤ 2 ^ (5 * n) * 31 := Nat.mul_le_mul_left _ (by omega)
    omega
lemma pk_add (n : ℕ) (f g : ℕ → ℕ) : pk n f + pk n g = pk n (fun j => f j + g j) := by
  simp [pk, ← Finset.sum_add_distrib, add_mul]
lemma pk_congr {n : ℕ} {f g : ℕ → ℕ} (h : ∀ j < n, f j = g j) : pk n f = pk n g :=
  Finset.sum_congr rfl fun j hj => by rw [h j (by simpa using hj)]
lemma pk_sub {n : ℕ} {f g : ℕ → ℕ} (h : ∀ j < n, g j ≤ f j) : pk n f - pk n g = pk n (fun j => f j - g j) := by
  have : pk n (fun j => f j - g j) + pk n g = pk n f := by
    rw [pk_add]; exact pk_congr fun j hj => Nat.sub_add_cancel (h j hj)
  omega
lemma pk_guard {n : ℕ} {f : ℕ → ℕ} (h : ∀ j < n, 16 ≤ f j ∧ f j < 32) :
    pk n f &&& pk n (fun _ => 16) = pk n (fun _ => 16) := by
  induction n with
  | zero => simp [pk]
  | succ n ih =>
    have ih := ih (fun j hj => h j (by omega))
    have h1 : pk n f < 2 ^ (5 * n) := pk_lt fun j hj => (h j (by omega)).2
    have h2 : pk n (fun _ => 16) < 2 ^ (5 * n) := pk_lt fun _ _ => by omega
    have h3 : f n &&& 16 = 16 := by
      obtain ⟨a, b⟩ := h n (by omega)
      generalize f n = x at *
      interval_cases x <;> rfl
    rw [pk_succ, pk_succ]
    apply Nat.eq_of_testBit_eq; intro i
    rw [Nat.testBit_and, Nat.testBit_two_pow_mul_add _ h1, Nat.testBit_two_pow_mul_add _ h2]
    split_ifs with hi
    · rw [← Nat.testBit_and, ih]
    · rw [← Nat.testBit_and, h3]
def isPk (n x : ℕ) : Prop := ∀ i, x.testBit i = true → i % 5 = 0 ∧ i / 5 < n
lemma pk_of {n : ℕ} : ∀ {x : ℕ}, isPk n x → x = pk n (fun j => (x.testBit (5 * j)).toNat) := by
  induction n with
  | zero =>
    intro x h
    simp only [pk, Finset.range_zero, Finset.sum_empty]
    apply Nat.eq_of_testBit_eq; intro i
    by_contra hc
    have := h i (by simpa using hc); omega
  | succ n ih =>
    intro x h
    have hm : isPk n (x % 2 ^ (5 * n)) := by
      intro i hi
      simp only [Nat.testBit_mod_two_pow, Bool.and_eq_true, decide_eq_true_eq] at hi
      exact ⟨(h i hi.2).1, by omega⟩
    have e := ih hm
    have hd : x / 2 ^ (5 * n) = (x.testBit (5 * n)).toNat := by
      apply Nat.eq_of_testBit_eq; intro i
      rw [Nat.testBit_div_two_pow]
      cases i with
      | zero => cases hb : x.testBit (5 * n) <;> simp [hb]
      | succ i =>
        have e1 : x.testBit (i + 1 + 5 * n) = false := by
          by_contra hc
          have := h _ (by simpa using hc); omega
        rw [e1]
        cases x.testBit (5 * n) <;> simp [Nat.testBit_succ]
    rw [pk_succ, ← hd]
    have e2 : pk n (fun j => (x.testBit (5 * j)).toNat) = x % 2 ^ (5 * n) := by
      conv_rhs => rw [e]
      refine pk_congr fun j hj => ?_
      rw [Nat.testBit_mod_two_pow]; simp [show 5 * j < 5 * n by omega]
    rw [e2]; exact (Nat.div_add_mod x _).symm
lemma isPk_and {n x y : ℕ} (hx : isPk n x) : isPk n (x &&& y) := fun i hi => hx i (by simp at hi; exact hi.1)
lemma isPk_or {n x y : ℕ} (hx : isPk n x) (hy : isPk n y) : isPk n (x ||| y) := fun i hi => by
  simp at hi; exact hi.elim (hx i) (hy i)
def fl (w : W) (j : ℕ) : ℕ := (w.c.testBit (5 * j)).toNat
lemma fl_le (w : W) (j : ℕ) : fl w j ≤ 1 := by unfold fl; cases w.c.testBit (5 * j) <;> simp
def cnt (v : List W) (j : ℕ) : ℕ := (v.map (fun w => fl w j)).sum
lemma cnt_cons (w : W) (v : List W) (j : ℕ) : cnt (w :: v) j = fl w j + cnt v j := by simp [cnt]
lemma cnt_perm {v v' : List W} (h : v.Perm v') (j : ℕ) : cnt v j = cnt v' j := (h.map _).sum_eq
structure WOk (P : List ℕ) (w : W) : Prop where
  pa : isPk P.length w.a
  pb : isPk P.length w.b
  ec : w.c = w.a ||| w.b
  ca : ∀ j < P.length, w.a.testBit (5 * j) = true → w.s &&& P.getD j 0 = 0
  cb : ∀ j < P.length, w.b.testBit (5 * j) = true → w.s &&& P.getD j 0 = P.getD j 0
lemma WOk.pc {P : List ℕ} {w : W} (h : WOk P w) : isPk P.length w.c := by rw [h.ec]; exact isPk_or h.pa h.pb
lemma WOk.cst {P : List ℕ} {w : W} (h : WOk P w) {j : ℕ} (hj : j < P.length) (hf : w.c.testBit (5 * j) = true) :
    Cst (P.getD j 0) w.s := by
  rw [h.ec, Nat.testBit_or, Bool.or_eq_true] at hf
  exact hf.elim (fun h1 => Or.inl (h.ca j hj h1)) (fun h1 => Or.inr (h.cb j hj h1))
def Cl (P : List ℕ) (T k : ℕ) (b : ℕ → ℕ) (S : Finset ℕ) : Prop := ∀ j < P.length, ∀ q, q + b j < k →
  ¬ Sol Z0 (P.getD j 0) (T &&& P.getD j 0) q (C (P.getD j 0) (Im (P.getD j 0) S))
structure StOk (P : List ℕ) (T l k z : ℕ) (v : List W) (S : Finset ℕ) : Prop where
  rep : Rep v S
  wok : ∀ w ∈ v, WOk P w
  good : ∀ w ∈ v, Good l w.s
  bud : ∃ b : ℕ → ℕ, (∀ j < P.length, b j ≤ 15) ∧ Cl P T k b S ∧ z = pk P.length (fun j => 16 + b j - cnt v j)
structure Ctx (P : List ℕ) (l m g T : ℕ) : Prop where
  lg : ∀ i, l.testBit i = true → Lg NN m T i ∧ AA.testBit i = true
  hP : ∀ j < P.length, P.getD j 0 &&& m = P.getD j 0 ∧ T &&& P.getD j 0 ≠ 0 ∧ T &&& P.getD j 0 ≠ P.getD j 0
  hg : g = pk P.length (fun _ => 16)
section sound
variable {P : List ℕ} {l m g T : ℕ} (X : Ctx P l m g T)
include X
lemma cnt_le {k k' t : ℕ} {v : List W} {S : Finset ℕ} {b : ℕ → ℕ} (hr : Rep v S) (hw : ∀ w ∈ v, WOk P w)
    (hc : Cl P T k b S) (hm : Min R m T k' t S) (hk : k' ≤ k) : ∀ j < P.length, cnt v j ≤ b j := by
  intro j hj
  obtain ⟨p1, p2, p3⟩ := X.hP j hj
  obtain ⟨q, hq, hs⟩ := hm.const p1 p2 p3
  have hqb : ¬ q + b j < k := fun h => hc j hj q h hs
  have : cnt v j ≤ (S.filter (Cst (P.getD j 0))).card := by
    have e : cnt v j = (v.filter (fun w => w.c.testBit (5 * j))).length := by
      clear hr hw
      induction v with
      | nil => rfl
      | cons w v ih =>
        rw [cnt_cons, ih, List.filter_cons, fl]
        cases w.c.testBit (5 * j) <;> simp; omega
    rw [e, ← List.length_map W.s, ← List.toFinset_card_of_nodup (hr.1.sublist (List.filter_sublist.map _))]
    apply Finset.card_le_card
    intro x hx
    simp only [List.mem_toFinset, List.mem_map, List.mem_filter] at hx
    obtain ⟨w, ⟨h1, h2⟩, rfl⟩ := hx
    rw [Finset.mem_filter]
    exact ⟨hr.mem.2 ⟨w, h1, rfl⟩, (hw w h1).cst hj h2⟩
  omega
lemma guard_ok {k k' t z : ℕ} {v : List W} {S : Finset ℕ} (hr : StOk P T l k z v S) (hm : Min R m T k' t S) (hk : k' ≤ k) :
    Nat.beq (Nat.land z g) g = true := by
  obtain ⟨b, hb, hc, hz⟩ := hr.bud
  have hle := cnt_le X hr.rep hr.wok hc hm hk
  rw [nl, hz, X.hg, pk_guard]; · simp
  intro j hj
  have := hb j hj; have := hle j hj; omega
lemma child_sound {f : ℕ → List W → Bool} {z t k k' : ℕ} {r : List W} {S : Finset ℕ}
    {mk : (List W → Bool) → Bool} (hmk : ∀ h, mk h = h r)
    (hr : StOk P T l k z r S) (hm : Min R m T k' t S) (hk : k' ≤ k) (h : child f g mk z = false) : f z r = false := by
  simp only [child, bR, st_eq, guard_ok X hr hm hk, cond_true, hmk] at h
  exact h
end sound
lemma rm_eq (x y : ℕ) (v : List W) : ∀ h, rm x y v h = h (v.filter (fun w => !(Nat.beq w.s x || Nat.beq w.s y))) := by
  induction v with
  | nil => intro h; rfl
  | cons w v ih =>
    intro h
    change (Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) (rm x y v (fun r => h (w :: r)))
      (rm x y v h) (Nat.beq w.s y)) (rm x y v h) (Nat.beq w.s x) : Bool) = _
    rw [bR, bR, ih, ih, List.filter_cons]
    cases Nat.beq w.s x <;> cases Nat.beq w.s y <;> simp
lemma ins_spec (o : W) (v : List W) (hv : ∀ w ∈ v, w.s ≠ o.s) : ∃ r : List W, r.Perm (o :: v) ∧ ∀ h, ins o v h = h r := by
  induction v with
  | nil => exact ⟨[o], List.Perm.refl _, fun h => rfl⟩
  | cons w v ih =>
    obtain ⟨r, hp, hr⟩ := ih fun w' hw' => hv w' (by simp [hw'])
    have e : ∀ h, ins o (w :: v) h = bif Nat.ble w.s o.s then (bif Nat.beq o.s w.s then false else h (o :: w :: v)) else ins o v (fun r => h (w :: r)) := by
      intro h
      change (Bool.rec (motive := fun _ => Bool) (ins o v (fun r => h (w :: r)))
        (Bool.rec (motive := fun _ => Bool) (h (o :: w :: v)) false (Nat.beq o.s w.s)) (Nat.ble w.s o.s) : Bool) = _
      rw [bR, bR]
    cases hb : Nat.ble w.s o.s with
    | true =>
      refine ⟨o :: w :: v, List.Perm.refl _, fun h => ?_⟩
      have : Nat.beq o.s w.s = false := Bool.eq_false_iff.2 fun h => hv w (by simp) (Nat.eq_of_beq_eq_true h).symm
      rw [e, hb, this]; rfl
    | false =>
      refine ⟨w :: r, (List.Perm.cons w hp).trans (List.Perm.swap _ _ _), fun h => ?_⟩
      rw [e, hb, hr]; rfl
lemma filter_perm {v : List W} (hv : (v.map W.s).Nodup) {a : W} (ha : a ∈ v) :
    (a :: v.filter (fun w => !Nat.beq w.s a.s)).Perm v := by
  induction v with
  | nil => simp at ha
  | cons w v ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and] at hv
    have hne : ∀ x y : ℕ, x ≠ y → Nat.beq x y = false := fun x y h => Bool.eq_false_iff.2 fun h' => h (Nat.eq_of_beq_eq_true h')
    simp only [List.mem_cons] at ha
    rcases ha with rfl | ha
    · have : v.filter (fun w => !Nat.beq w.s a.s) = v := by
        rw [List.filter_eq_self]
        intro w' hw'
        rw [hne _ _ (hv.1 w' hw')]; rfl
      rw [List.filter_cons, this]; simp
    · rw [List.filter_cons, hne w.s a.s (fun e => hv.1 a ha e.symm)]
      simp only [Bool.not_false, if_true]
      exact (List.Perm.swap _ _ _).trans ((ih hv.2 ha).cons w)
lemma filter2 {v : List W} {x y : ℕ} : v.filter (fun w => !(Nat.beq w.s x || Nat.beq w.s y)) =
    (v.filter (fun w => !Nat.beq w.s x)).filter (fun w => !Nat.beq w.s y) := by
  rw [List.filter_filter]; congr 1; funext w; cases Nat.beq w.s x <;> cases Nat.beq w.s y <;> rfl
lemma filter1 {v : List W} {x : ℕ} : v.filter (fun w => !(Nat.beq w.s x || Nat.beq w.s x)) = v.filter (fun w => !Nat.beq w.s x) := by
  congr 1; funext w; cases Nat.beq w.s x <;> rfl
inductive Shape (o a c : W) (v : List W) : Bool → Bool → List W → Prop
  | ff {r} : (a :: c :: r).Perm (o :: v) → Shape o a c v false false r
  | tf {r} : (c :: r).Perm (o :: v) → Shape o a c v true false r
  | ft {r} : (a :: r).Perm (o :: v) → Shape o a c v false true r
  | tt {r} : r.Perm (o :: v) → Shape o a c v true true r
lemma Shape.cnt {o a c : W} {v r : List W} {ka kc : Bool} (h : Shape o a c v ka kc r) (j : ℕ) :
    cnt r j + (bif ka then 0 else fl a j) + (bif kc then 0 else fl c j) = fl o j + cnt v j := by
  cases h with
  | ff h => have := cnt_perm h j; simp only [cnt_cons] at this; simp; omega
  | tf h => have := cnt_perm h j; simp only [cnt_cons] at this; simp; omega
  | ft h => have := cnt_perm h j; simp only [cnt_cons] at this; simp; omega
  | tt h => have := cnt_perm h j; simp only [cnt_cons] at this; simp; omega
lemma Shape.mem {o a c : W} {v r : List W} {ka kc : Bool} (h : Shape o a c v ka kc r) {w : W} (hw : w ∈ r) : w = o ∨ w ∈ v := by
  have : w ∈ o :: v := by
    cases h with
    | ff h => exact h.subset (by simp [hw])
    | tf h => exact h.subset (by simp [hw])
    | ft h => exact h.subset (by simp [hw])
    | tt h => exact h.subset (by simp [hw])
  simpa using this
lemma Shape.len {o a c : W} {v r : List W} {ka kc : Bool} (h : Shape o a c v ka kc r) :
    r.length + (bif ka then 0 else 1) + (bif kc then 0 else 1) = v.length + 1 := by
  cases h with
  | ff h => have := h.length_eq; simp at this ⊢; omega
  | tf h => have := h.length_eq; simp at this ⊢; omega
  | ft h => have := h.length_eq; simp at this ⊢; omega
  | tt h => have := h.length_eq; simp at this ⊢; omega
lemma Shape.rep {o a c : W} {v r : List W} {ka kc : Bool} (h : Shape o a c v ka kc r) {S S' : Finset ℕ} (hr : Rep v S)
    (ha : a ∈ v) (hc : c ∈ v) (hac : a.s ≠ c.s) (ho : o.s ∉ S)
    (hS : ∀ x, x ∈ S' ↔ x = o.s ∨ (x ∈ S ∧ (x = a.s → ka = true) ∧ (x = c.s → kc = true))) : Rep r S' := by
  have hov : ((o :: v).map W.s).Nodup := by
    simp only [List.map_cons, List.nodup_cons]
    refine ⟨fun hm => ho ?_, hr.1⟩
    rw [← hr.2]; simpa using hm
  have hvS : ∀ x, x ∈ v.map W.s ↔ x ∈ S := fun x => by rw [← hr.2]; simp
  have hm : ∀ x, x ∈ (o :: v).map W.s ↔ x = o.s ∨ x ∈ S := fun x => by simp only [List.map_cons, List.mem_cons, hvS]
  have haS := (hvS a.s).1 (List.mem_map_of_mem ha)
  have hcS := (hvS c.s).1 (List.mem_map_of_mem hc)
  have hao : a.s ≠ o.s := fun e => ho (e ▸ haS)
  have hco : c.s ≠ o.s := fun e => ho (e ▸ hcS)
  cases h with
  | ff h =>
    have hn := (h.map W.s).nodup_iff.2 hov
    simp only [List.map_cons, List.nodup_cons, List.mem_cons, not_or] at hn
    refine ⟨hn.2.2, Finset.ext fun x => ?_⟩
    have hx := (h.map W.s).mem_iff (a := x)
    rw [hm] at hx; simp only [List.map_cons, List.mem_cons] at hx
    rw [List.mem_toFinset, hS]
    constructor
    · intro h1
      have n1 : x ≠ a.s := fun e => hn.1.2 (e ▸ h1)
      have n2 : x ≠ c.s := fun e => hn.2.1 (e ▸ h1)
      rcases hx.1 (Or.inr (Or.inr h1)) with e | e
      · exact Or.inl e
      · exact Or.inr ⟨e, fun e => absurd e n1, fun e => absurd e n2⟩
    · rintro (e | ⟨e, f1, f2⟩)
      · rcases hx.2 (Or.inl e) with e' | e' | e'
        · exact absurd (e'.symm.trans e) hao
        · exact absurd (e'.symm.trans e) hco
        · exact e'
      · rcases hx.2 (Or.inr e) with e' | e' | e'
        · exact absurd (f1 e') (by simp)
        · exact absurd (f2 e') (by simp)
        · exact e'
  | tf h =>
    have hn := (h.map W.s).nodup_iff.2 hov
    simp only [List.map_cons, List.nodup_cons] at hn
    refine ⟨hn.2, Finset.ext fun x => ?_⟩
    have hx := (h.map W.s).mem_iff (a := x)
    rw [hm] at hx; simp only [List.map_cons, List.mem_cons] at hx
    rw [List.mem_toFinset, hS]
    constructor
    · intro h1
      have n2 : x ≠ c.s := fun e => hn.1 (e ▸ h1)
      rcases hx.1 (Or.inr h1) with e | e
      · exact Or.inl e
      · exact Or.inr ⟨e, fun _ => rfl, fun e => absurd e n2⟩
    · rintro (e | ⟨e, f1, f2⟩)
      · exact (hx.2 (Or.inl e)).resolve_left fun e' => hco (e'.symm.trans e)
      · exact (hx.2 (Or.inr e)).resolve_left fun e' => by simpa using f2 e'
  | ft h =>
    have hn := (h.map W.s).nodup_iff.2 hov
    simp only [List.map_cons, List.nodup_cons] at hn
    refine ⟨hn.2, Finset.ext fun x => ?_⟩
    have hx := (h.map W.s).mem_iff (a := x)
    rw [hm] at hx; simp only [List.map_cons, List.mem_cons] at hx
    rw [List.mem_toFinset, hS]
    constructor
    · intro h1
      have n2 : x ≠ a.s := fun e => hn.1 (e ▸ h1)
      rcases hx.1 (Or.inr h1) with e | e
      · exact Or.inl e
      · exact Or.inr ⟨e, fun e => absurd e n2, fun _ => rfl⟩
    · rintro (e | ⟨e, f1, f2⟩)
      · exact (hx.2 (Or.inl e)).resolve_left fun e' => hao (e'.symm.trans e)
      · exact (hx.2 (Or.inr e)).resolve_left fun e' => by simpa using f1 e'
  | tt h =>
    have hn := (h.map W.s).nodup_iff.2 hov
    refine ⟨hn, Finset.ext fun x => ?_⟩
    have hx := (h.map W.s).mem_iff (a := x)
    rw [hm] at hx
    rw [List.mem_toFinset, hS, hx]; simp
lemma shape_all {o a c : W} {v r : List W} (ho : ∀ w ∈ v, w.s ≠ o.s) (hp : r.Perm (o :: v)) (hv : (v.map W.s).Nodup)
    (ha : a ∈ v) (hc : c ∈ v) (hac : a.s ≠ c.s) :
    Shape o a c v false false (r.filter (fun w => !(Nat.beq w.s a.s || Nat.beq w.s c.s))) ∧
    Shape o a c v true false (r.filter (fun w => !(Nat.beq w.s c.s || Nat.beq w.s c.s))) ∧
    Shape o a c v false true (r.filter (fun w => !(Nat.beq w.s a.s || Nat.beq w.s a.s))) ∧ Shape o a c v true true r := by
  have hnd : (r.map W.s).Nodup := by
    refine (hp.map W.s).nodup_iff.2 ?_
    simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and]
    exact ⟨fun w hw => ho w hw, hv⟩
  have har : a ∈ r := hp.symm.subset (by simp [ha])
  have hcr : c ∈ r := hp.symm.subset (by simp [hc])
  refine ⟨.ff ?_, .tf ?_, .ft ?_, .tt hp⟩
  · rw [filter2]
    have h1 := filter_perm hnd har
    have h2 : c ∈ r.filter (fun w => !Nat.beq w.s a.s) := by
      rw [List.mem_filter]; refine ⟨hcr, ?_⟩
      rw [Bool.eq_false_iff.2 fun h => hac (Nat.eq_of_beq_eq_true h).symm]; rfl
    exact ((filter_perm (hnd.sublist (List.filter_sublist.map _)) h2).cons a).trans (h1.trans hp)
  · rw [filter1]; exact (filter_perm hnd hcr).trans hp
  · rw [filter1]; exact (filter_perm hnd har).trans hp
lemma cnt_two {v : List W} {a c : W} (ha : a ∈ v) (hc : c ∈ v) (hv : (v.map W.s).Nodup) (hac : a.s ≠ c.s) (j : ℕ) :
    fl a j + fl c j ≤ cnt v j := by
  have h1 := cnt_perm (filter_perm hv ha) j
  have h2 : c ∈ v.filter (fun w => !Nat.beq w.s a.s) := by
    rw [List.mem_filter]; refine ⟨hc, ?_⟩
    rw [Bool.eq_false_iff.2 fun h => hac (Nat.eq_of_beq_eq_true h).symm]; rfl
  have h3 := cnt_perm (filter_perm (hv.sublist (List.filter_sublist.map _)) h2) j
  simp only [cnt_cons] at h1 h3; omega
lemma cnt_one {v : List W} {a : W} (ha : a ∈ v) (hv : (v.map W.s).Nodup) (j : ℕ) : fl a j ≤ cnt v j := by
  have h1 := cnt_perm (filter_perm hv ha) j
  simp only [cnt_cons] at h1; omega
def opW (d : Bool) (a c : W) : W := bif d then ⟨a.s ||| c.s, a.a &&& c.a, a.b ||| c.b, (a.a &&& c.a) ||| (a.b ||| c.b), 0⟩
  else ⟨a.s &&& c.s, a.a ||| c.a, a.b &&& c.b, (a.a ||| c.a) ||| (a.b &&& c.b), 0⟩
lemma opW_s (d : Bool) (a c : W) : (opW d a c).s = op d a.s c.s := by cases d <;> rfl
lemma opW_ok {P : List ℕ} {a c : W} (d : Bool) (ha : WOk P a) (hc : WOk P c) : WOk P (opW d a c) := by
  cases d
  · refine ⟨isPk_or ha.pa hc.pa, isPk_and ha.pb, rfl, fun j hj h => ?_, fun j hj h => ?_⟩
    · have h : (a.a ||| c.a).testBit (5 * j) = true := h
      rw [Nat.testBit_or, Bool.or_eq_true] at h
      rw [opW_s, and_op]
      rcases h with h | h
      · rw [ha.ca j hj h]; simp [op]
      · rw [hc.ca j hj h]; simp [op]
    · have h : (a.b &&& c.b).testBit (5 * j) = true := h
      rw [Nat.testBit_and, Bool.and_eq_true] at h
      rw [opW_s, and_op, ha.cb j hj h.1, hc.cb j hj h.2, op_self]
  · refine ⟨isPk_and ha.pa, isPk_or ha.pb hc.pb, rfl, fun j hj h => ?_, fun j hj h => ?_⟩
    · have h : (a.a &&& c.a).testBit (5 * j) = true := h
      rw [Nat.testBit_and, Bool.and_eq_true] at h
      rw [opW_s, and_op, ha.ca j hj h.1, hc.ca j hj h.2, op_self]
    · have h : (a.b ||| c.b).testBit (5 * j) = true := h
      rw [Nat.testBit_or, Bool.or_eq_true] at h
      rw [opW_s, and_op]
      rcases h with h | h
      · rw [ha.cb j hj h]; apply Nat.eq_of_testBit_eq; intro i; simp [op]
      · rw [hc.cb j hj h]; apply Nat.eq_of_testBit_eq; intro i; simp [op]
lemma op_good {l x y : ℕ} (d : Bool) (hx : Good l x) (hy : Good l y) : Good l (op d x y) := by
  refine ⟨fun i j h h1 h2 => ?_, fun i j h h1 h2 => ?_⟩
  · rw [op_bit, op_bit, hx.1 i j h h1 h2, hy.1 i j h h1 h2]
  · rw [op_bit, op_bit, hx.2 i j h h1 h2, hy.2 i j h h1 h2]
lemma fl_and {P : List ℕ} {a c : W} (ha : WOk P a) : a.c &&& c.c = pk P.length (fun j => fl a j * fl c j) := by
  rw [pk_of (isPk_and (y := c.c) ha.pc)]
  refine pk_congr fun j _ => ?_
  rw [Nat.testBit_and]; unfold fl; cases a.c.testBit (5 * j) <;> cases c.c.testBit (5 * j) <;> rfl
lemma fl_pk {P : List ℕ} {a : W} (ha : WOk P a) : a.c = pk P.length (fl a) := pk_of ha.pc
section sound
variable {P : List ℕ} {l m g T : ℕ} (X : Ctx P l m g T)
include X
lemma bi_st {k k' t z : ℕ} {v r : List W} {S S' : Finset ℕ} {d' : Bool} {a c : W} {ka kc : Bool}
    (hs : StOk P T l (k + 1) z v S) (hm : Min R m T (k' + 1) t S) (hk : k' ≤ k) (hb : Bi R d' a.s c.s S S')
    (hl : Live R m T k' t S') (ha : a ∈ v) (hc : c ∈ v) (hka : ka = decide (a.s ∈ S')) (hkc : kc = decide (c.s ∈ S'))
    (hsh : Shape (opW d' a c) a c v ka kc r) :
    StOk P T l k (z + (a.c &&& c.c) - (opW d' a c).c - (bif ka then a.c else 0) - (bif kc then c.c else 0)) r S' ∧
    Nat.beq (Nat.land (z + (a.c &&& c.c) - (opW d' a c).c) g) g = true := by
  obtain ⟨b, hb15, hcl, hz⟩ := hs.bud
  have hle := cnt_le X hs.rep hs.wok hcl hm (by omega)
  have hab : a.s ≠ c.s := hb.1
  have hfr := hb.fresh hl hm.2
  have hfS : (opW d' a c).s ∉ S := by rw [opW_s]; exact fun h => hfr (sub_C _ _ (by simpa using h))
  have wa := hs.wok a ha; have wc := hs.wok c hc
  have wo := opW_ok d' wa wc
  have hrep : Rep r S' := by
    refine hsh.rep hs.rep ha hc hab hfS fun x => ?_
    obtain ⟨_, U, e1, e2, _⟩ := hb
    rw [opW_s] at hfS ⊢
    rw [e2, Finset.mem_insert]
    constructor
    · rintro (h | h)
      · exact Or.inl h
      · refine Or.inr ⟨by rw [e1]; simp [h], ?_, ?_⟩
        · rintro rfl; rw [hka, e2]; simp [h]
        · rintro rfl; rw [hkc, e2]; simp [h]
    · rintro (h | ⟨h, f1, f2⟩)
      · exact Or.inl h
      · rw [e1] at h; simp only [Finset.mem_insert] at h
        rcases h with h | h | h
        · have := f1 h; rw [hka, decide_eq_true_eq, e2, Finset.mem_insert] at this; rw [h]; exact this
        · have := f2 h; rw [hkc, decide_eq_true_eq, e2, Finset.mem_insert] at this; rw [h]; exact this
        · exact Or.inr h
  have hwok : ∀ w ∈ r, WOk P w := fun w hw => (hsh.mem hw).elim (fun e => e ▸ wo) (hs.wok w)
  have hgood : ∀ w ∈ r, Good l w.s := fun w hw => by
    rcases hsh.mem hw with rfl | h
    · rw [opW_s]; exact op_good _ (hs.good a ha) (hs.good c hc)
    · exact hs.good w h
  let b' : ℕ → ℕ := fun j => b j - max (fl a j) (fl c j)
  have hcl' : Cl P T k b' S' := by
    intro j hj q hq hsol
    have hl1 := hle j hj
    have h2 := cnt_two ha hc hs.rep.1 hab j
    simp only [b'] at hq
    by_cases hkill : a.c.testBit (5 * j) = true ∨ c.c.testBit (5 * j) = true
    · refine hcl j hj q ?_ (hb.kill (hkill.imp (wa.cst hj) (wc.cst hj)) hsol)
      have : 1 ≤ max (fl a j) (fl c j) := by
        rcases hkill with h | h <;> simp [fl, h]
      have := fl_le a j; have := fl_le c j; omega
    · push Not at hkill
      refine hcl j hj (q + 1) ?_ (hb.im hsol)
      have e1 : fl a j = 0 := by simp [fl, hkill.1]
      have e2 : fl c j = 0 := by simp [fl, hkill.2]
      rw [e1, e2] at hq; simp at hq; omega
  have hmin := hb.min hl hm.2
  have hle' := cnt_le X hrep hwok hcl' hmin hk
  have num : ∀ j < P.length, 1 ≤ 16 + b j - cnt v j + fl a j * fl c j ∧ fl (opW d' a c) j ≤ 1 ∧
      16 ≤ 16 + b j - cnt v j + fl a j * fl c j - fl (opW d' a c) j ∧ 16 + b j - cnt v j + fl a j * fl c j - fl (opW d' a c) j < 32 ∧
      16 + b j - cnt v j + fl a j * fl c j - fl (opW d' a c) j - (bif ka then fl a j else 0) - (bif kc then fl c j else 0) = 16 + b' j - cnt r j := by
    intro j hj
    have q1 := hle j hj; have q2 := hle' j hj; have q3 := cnt_two ha hc hs.rep.1 hab j; have q4 := hb15 j hj
    have q5 := hsh.cnt j; have q6 := fl_le a j; have q7 := fl_le c j; have q8 := fl_le (opW d' a c) j
    simp only [b'] at q2 ⊢
    generalize fl a j = fa at *; generalize fl c j = fc at *; generalize fl (opW d' a c) j = fo at *
    interval_cases fa <;> interval_cases fc <;> cases ka <;> cases kc <;> simp at q2 q3 q5 ⊢ <;> omega
  have e1 : z + (a.c &&& c.c) - (opW d' a c).c = pk P.length (fun j => 16 + b j - cnt v j + fl a j * fl c j - fl (opW d' a c) j) := by
    rw [hz, fl_and wa, fl_pk wo, pk_add, pk_sub]
    intro j hj; have := num j hj; omega
  refine ⟨⟨hrep, hwok, hgood, b', fun j hj => ?_, hcl', ?_⟩, ?_⟩
  · have := hb15 j hj; simp only [b']; omega
  · rw [e1]
    have ea : (bif ka then a.c else 0) = pk P.length (fun j => bif ka then fl a j else 0) := by
      cases ka
      · simp [pk]
      · exact fl_pk wa
    have ec : (bif kc then c.c else 0) = pk P.length (fun j => bif kc then fl c j else 0) := by
      cases kc
      · simp [pk]
      · exact fl_pk wc
    have le1 : ∀ j, (bif ka then fl a j else 0) ≤ 1 := fun j => by cases ka <;> simp [fl_le]
    have le2 : ∀ j, (bif kc then fl c j else 0) ≤ 1 := fun j => by cases kc <;> simp [fl_le]
    rw [ea, ec, pk_sub, pk_sub]
    · exact pk_congr fun j hj => (num j hj).2.2.2.2
    · intro j hj; have := num j hj; have := le1 j; have := le2 j; omega
    · intro j hj; have := num j hj; have := le1 j; omega
  · rw [e1, nl, X.hg, pk_guard]; · simp
    intro j hj; have := num j hj; omega
lemma drop_ok {k' t : ℕ} {v : List W} {S S' : Finset ℕ} {d' : Bool} {a c : W} {i : ℕ} (hr : Rep v S)
    (hb : Bi R d' a.s c.s S S') (hl : Live R m T k' t S')
    (ha : a ∈ v) (hk : a.s ∉ S')
    (hu : (Nat.land (sp (pos' t) l a.s) (wst (pos' t) l v)).testBit i = true) :
    bif d' then c.s.testBit (NN + i) = false else c.s.testBit i = true := by
  obtain ⟨hli, u1, u2⟩ := uq_of hr ha hu
  obtain ⟨⟨m1, m2, t1, t2⟩, _⟩ := X.lg i hli
  obtain ⟨w, hw, hs⟩ := hl.cov m1 m2 t1 t2
  have hac : c.s ≠ a.s := hb.1.symm
  have hsub := hb.sub.2.2 hw
  rw [Finset.mem_insert] at hsub
  have hg : sepb NN (pos' t) (op d' a.s c.s) i = true := by
    rcases hsub with rfl | h
    · exact hs
    · have := u2 w h (fun e => hk (e ▸ hw))
      rw [this] at hs; simp at hs
  have hcn := u2 c.s hb.sub.2.1 hac
  revert hg hcn u1
  unfold sepb; simp only [op_bit]
  cases pos' t <;> cases d' <;> cases a.s.testBit i <;> cases a.s.testBit (NN + i) <;> cases c.s.testBit i <;>
    cases c.s.testBit (NN + i) <;> simp
end sound
def mkx (d : Bool) (l o : ℕ) (w : W) : X := ⟨w, w.s, Nat.shiftRight w.s NN, Nat.land (sp d l w.s) o⟩
lemma mkX_eq (d : Bool) (l o : ℕ) (v : List W) : mkX d l o v = v.map (mkx d l o) := by
  induction v with
  | nil => rfl
  | cons w v ih => change _ :: mkX d l o v = _; rw [ih]; rfl
def modeF (n e : ℕ) : (W → W → ℕ → ℕ → ℕ → ℕ → ℕ → Bool) → W → W → ℕ → ℕ → ℕ → ℕ → ℕ → Bool :=
  bif Nat.ble n e then (bif Nat.ble (Nat.succ n) e then f2 else f1) else f0
lemma node_eq (f : ℕ → List W → Bool) (d : Bool) (l m g e n z : ℕ) (v : List W) (go : (X → X → Bool) → List X → Bool) :
    node f d l m g e n z v go = go (pair (modeF n e (mid f m g e (Nat.pred n) z v))) (v.map (mkx d l (wst d l v))) := by
  rw [← mkX_eq]; unfold node modeF
  cases Nat.ble n e <;> cases Nat.ble (Nat.succ n) e <;> rfl
lemma modeF_false {n e : ℕ} {h : W → W → ℕ → ℕ → ℕ → ℕ → ℕ → Bool} {a c : W} {da dc : ℕ} {s x y : ℕ}
    (hf : modeF n e h a c da dc s x y = false) (h0 : ¬ n ≤ e → da = 0 ∧ dc = 0) (h1 : ¬ n + 1 ≤ e → da = 0 ∨ dc = 0) :
    h a c da dc s x y = false := by
  unfold modeF at hf
  cases b1 : Nat.ble n e with
  | false =>
    have := h0 (fun h => by rw [Nat.ble_eq_true_of_le h] at b1; simp at b1)
    rw [b1, this.1, this.2] at hf; rw [this.1, this.2]; exact hf
  | true =>
    cases b2 : Nat.ble (Nat.succ n) e with
    | false =>
      have := h1 (fun h => by rw [Nat.ble_eq_true_of_le h] at b2; simp at b2)
      have h3 : Nat.beq (Nat.mul da dc) 0 = true := by
        change Nat.beq (da * dc) 0 = true
        rcases this with h | h <;> simp [h]
      rw [b1, b2] at hf
      simp only [Bool.cond_true, Bool.cond_false, f1, h3] at hf
      exact hf
    | true => rw [b1, b2] at hf; exact hf
def dfc (d d' : Bool) (l o : ℕ) (a c : W) : ℕ := bif d' then Nat.land (Nat.land (sp d l a.s) o) (Nat.shiftRight c.s NN)
  else Nat.xor (Nat.land (Nat.land (sp d l a.s) o) c.s) (Nat.land (sp d l a.s) o)
lemma pair_false {h : W → W → ℕ → ℕ → ℕ → ℕ → ℕ → Bool} {d : Bool} {l o : ℕ} {a c : W}
    (hp : pair h (mkx d l o a) (mkx d l o c) = false) (d' : Bool) :
    h a c (dfc d d' l o a c) (dfc d d' l o c a) (opW d' a c).s (opW d' a c).a (opW d' a c).b = false := by
  simp only [pair, mkx, bR] at hp
  rw [Bool.cond_eq_ite] at hp
  split_ifs at hp with h1
  · cases d'
    · rw [Bool.not_eq_true] at h1; exact h1
    · exact hp
lemma put_eq {m : ℕ} {o : W} {v : List W} (ho : Nat.lor o.a o.b = o.c) (hr : o.r = 0) (h0 : o.s ≠ 0) (h1 : o.s ≠ m) (h : List W → Bool) :
    put m o.s o.a o.b v h = ins o v h := by
  have hb0 : Nat.beq o.s 0 = false := Bool.eq_false_iff.2 fun h => h0 (Nat.eq_of_beq_eq_true h)
  have hb1 : Nat.beq o.s m = false := Bool.eq_false_iff.2 fun h => h1 (Nat.eq_of_beq_eq_true h)
  simp only [put, st_eq, hb0, hb1, ho]
  rw [← hr]
lemma mid_false {f : ℕ → List W → Bool} {m g e n z : ℕ} {v : List W} {a c : W} {da dc : ℕ} {d' : Bool}
    (h : mid f m g e n z v a c da dc (opW d' a c).s (opW d' a c).a (opW d' a c).b = false)
    (hg : Nat.beq (Nat.land (z + (a.c &&& c.c) - (opW d' a c).c) g) g = true) :
    kids (child f g) e n (z + (a.c &&& c.c) - (opW d' a c).c) a.c c.c a.s c.s (Nat.beq da 0) (Nat.beq dc 0)
      (put m (opW d' a c).s (opW d' a c).a (opW d' a c).b v) = false := by
  have ec : Nat.lor (opW d' a c).a (opW d' a c).b = (opW d' a c).c := by cases d' <;> rfl
  simp only [mid, st_eq, ec] at h
  have hg' : Nat.beq (Nat.land (Nat.sub (Nat.add z (Nat.land a.c c.c)) (opW d' a c).c) g) g = true := hg
  rw [hg'] at h
  exact h
lemma kids_false {ch : ((List W → Bool) → Bool) → ℕ → Bool} {e n z x y a c : ℕ} {oa oc : Bool} {mk : (List W → Bool) → Bool}
    (h : kids ch e n z x y a c oa oc mk = false) :
    (oa = true → oc = true → ch (fun h => mk (fun r => rm a c r h)) z = false) ∧
    (oc = true → n + 1 ≤ e → ch (fun h => mk (fun r => rm c c r h)) (z - x) = false) ∧
    (oa = true → n + 1 ≤ e → ch (fun h => mk (fun r => rm a a r h)) (z - y) = false) ∧
    (n + 2 ≤ e → ch mk (z - x - y) = false) := by
  simp only [kids, bR] at h
  have b1 : n + 1 ≤ e → Nat.ble (Nat.succ n) e = true := fun h => Nat.ble_eq_true_of_le h
  have b2 : n + 2 ≤ e → Nat.ble (Nat.succ (Nat.succ n)) e = true := fun h => Nat.ble_eq_true_of_le h
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h1 h2; subst h1 h2
    revert h; simp only [Bool.cond_true]; cases ch (fun h => mk (fun r => rm a c r h)) z <;> simp
  · intro h1 h2; subst h1; rw [b1 h2] at h
    revert h; simp only [Bool.cond_true]
    change _ → ch (fun h => mk (fun r => rm c c r h)) (Nat.sub z x) = false
    cases ch (fun h => mk (fun r => rm c c r h)) (Nat.sub z x) <;> simp
  · intro h1 h2; subst h1; rw [b1 h2] at h
    revert h; simp only [Bool.cond_true]
    change _ → ch (fun h => mk (fun r => rm a a r h)) (Nat.sub z y) = false
    cases ch (fun h => mk (fun r => rm a a r h)) (Nat.sub z y) <;> simp
  · intro h2; rw [b2 h2] at h
    revert h; simp only [Bool.cond_true]
    change _ → ch mk (Nat.sub (Nat.sub z x) y) = false
    cases ch mk (Nat.sub (Nat.sub z x) y) <;> simp
lemma Live.rel {R' : ℕ → ℕ} {m T k t : ℕ} {S : Finset ℕ} (h : Live R m T k t S) (hR : ∀ d a b, Al R d a b → Al R' d a b) : Live R' m T k t S := by
  induction h with
  | stop => exact .stop
  | un _ ih => exact .un ih
  | bi hab hal _ ih => exact .bi hab (hR _ _ _ hal) ih
lemma Bi.rel {R' : ℕ → ℕ} {a b : ℕ} {d : Bool} {S S' : Finset ℕ} (h : Bi R d a b S S') (hR : ∀ d a b, Al R d a b → Al R' d a b) : Bi R' d a b S S' := by
  obtain ⟨hab, U, e1, e2, hal⟩ := h; exact ⟨hab, U, e1, e2, hR _ _ _ hal⟩
section sound
variable {P : List ℕ} {l m g T : ℕ} (X : Ctx P l m g T)
include X
lemma rect_ok {t k k' z : ℕ} {r : List W} {S : Finset ℕ} (hr : StOk P T l k z r S) (hm : Min R m T k' t S) (hk : k' ≤ k)
    (hn : r.length + t = k + 1) : rect (pos' t) l (wst (pos' t) l r) r [] = false := by
  cases hrect : rect (pos' t) l (wst (pos' t) l r) r [] with
  | false => rfl
  | true =>
      exfalso
      have hs := hm.size
      have hcard := hr.rep.card
      have hpos : 0 < S.card := hm.1.pos
      have htight : S.card + t = k' + 1 := by omega
      rw [rect_false (o := wst (pos' t) l r)] at hrect; · simp at hrect
      · have hnd : r.Pairwise (fun a b => a.s ≠ b.s) := List.pairwise_map.1 hr.rep.1
        refine hnd.imp_of_mem fun {a b} ha hb' hab => ?_
        by_contra hhit
        rw [Bool.not_eq_false] at hhit
        obtain ⟨⟨s, hs1, x1, x2⟩, ⟨s', hs2, y1, y2⟩⟩ := hit_spec hhit
        have hu : ∀ w, ∀ i, (Nat.land (sp (pos' t) l w) (wst (pos' t) l r)).testBit i = true → AA.testBit i = true := by
          intro w i hi
          simp only [nl, Nat.testBit_and, sp_bit, Bool.and_eq_true] at hi
          exact (X.lg i hi.1.1).2
        obtain ⟨i2, b1, b2, b3⟩ := flag_seg segX_ok (hu b.s) hs1 x1
        obtain ⟨i1, a1, a2, a3⟩ := flag_seg segX_ok (hu a.s) hs1 x2
        obtain ⟨j2, d1, d2, d3⟩ := flag_seg segY_ok (hu b.s) hs2 y1
        obtain ⟨j1, c1, c2, c3⟩ := flag_seg segY_ok (hu a.s) hs2 y2
        obtain ⟨l1, u1⟩ := uq_of hr.rep ha a3
        obtain ⟨l2, u2⟩ := uq_of hr.rep hb' b3
        obtain ⟨l3, u3⟩ := uq_of hr.rep ha c3
        obtain ⟨l4, u4⟩ := uq_of hr.rep hb' d3
        have g1 : ∀ w ∈ S, w.testBit i1 = w.testBit i2 := by
          intro w hw; obtain ⟨w', hw', rfl⟩ := hr.rep.mem.1 hw
          exact (hr.good w' hw').1 _ _ ⟨s, hs1, a1, a2, b1, b2⟩ l1 l2
        have g2 : ∀ w ∈ S, w.testBit (NN + j1) = w.testBit (NN + j2) := by
          intro w hw; obtain ⟨w', hw', rfl⟩ := hr.rep.mem.1 hw
          exact (hr.good w' hw').2 _ _ ⟨s', hs2, c1, c2, d1, d2⟩ l3 l4
        have ma := hr.rep.mem.2 ⟨a, ha, rfl⟩
        have mb := hr.rep.mem.2 ⟨b, hb', rfl⟩
        rcases Nat.eq_zero_or_pos t with rfl | htp
        · have hd' : pos' 0 = false := by simp [pos']
          rw [hd'] at u1 u2 u3 u4
          exact rect0 hm.1 hm.2 (by simpa using htight) (X.lg _ l1).1 (X.lg _ l2).1 (X.lg _ l3).1 (X.lg _ l4).1
            ma mb hab g1 g2 u1 u2 u3 u4
        · have hd' : pos' t = true := by simp [pos', htp]
          rw [hd'] at u1 u2 u3 u4
          exact rect1 hm.1 hm.2 htight (X.lg _ l1).1 (X.lg _ l2).1 (X.lg _ l3).1 (X.lg _ l4).1
            ma mb hab g1 g2 u1 u2 u3 u4
      · simp
lemma hit_ht {k z : ℕ} {r : List W} {S : Finset ℕ} {d : Bool} (hr : StOk P T l k z r S) {a b : W} (ha : a ∈ r) (hb : b ∈ r)
    (h : hit (flag false l (wst d l r) a) (flag false l (wst d l r) b) = true) : Ht NN m T d S a.s b.s := by
  obtain ⟨⟨s, hs1, x1, x2⟩, ⟨s', hs2, y1, y2⟩⟩ := hit_spec h
  have hu : ∀ w, ∀ i, (Nat.land (sp false l w) (wst d l r)).testBit i = true → AA.testBit i = true := by
    intro w i hi
    simp only [nl, Nat.testBit_and, sp_bit, Bool.and_eq_true] at hi
    exact (X.lg i hi.1.1).2
  have uq : ∀ {w : W} {i : ℕ}, w ∈ r → (Nat.land (sp false l w.s) (wst d l r)).testBit i = true →
      l.testBit i = true ∧ Uq NN d S w.s i ∧ w.s.testBit i = true := by
    intro w i hw hi
    have hi2 := hi
    simp only [nl, Nat.testBit_and, sp_bit, Bool.and_eq_true] at hi2
    obtain ⟨⟨hl, hs⟩, ho⟩ := hi2
    have hsd : sepb NN d w.s i = true := by
      cases d
      · exact hs
      · exact sepb_weak _ hs
    obtain ⟨q1, q2⟩ := uq_of hr.rep hw (d := d) (l := l) (i := i) (by
      simp only [nl, Nat.testBit_and, sp_bit, Bool.and_eq_true]; exact ⟨⟨hl, hsd⟩, ho⟩)
    refine ⟨q1, q2, ?_⟩
    revert hs; simp only [sepb, cond_false]; cases w.s.testBit i <;> simp
  obtain ⟨i1, a1, a2, a3⟩ := flag_seg segX_ok (hu a.s) hs1 x1
  obtain ⟨i2, b1, b2, b3⟩ := flag_seg segX_ok (hu b.s) hs1 x2
  obtain ⟨j1, c1, c2, c3⟩ := flag_seg segY_ok (hu a.s) hs2 y1
  obtain ⟨j2, d1, d2, d3⟩ := flag_seg segY_ok (hu b.s) hs2 y2
  obtain ⟨l1, u1, p1⟩ := uq ha a3
  obtain ⟨l2, u2, p2⟩ := uq hb b3
  obtain ⟨l3, u3, p3⟩ := uq ha c3
  obtain ⟨l4, u4, p4⟩ := uq hb d3
  refine ⟨i1, i2, j1, j2, (X.lg _ l1).1, (X.lg _ l2).1, (X.lg _ l3).1, (X.lg _ l4).1, ?_, ?_, u1, u2, u3, u4, by rw [p1, p3], by rw [p2, p4]⟩
  · intro w hw; obtain ⟨w', hw', rfl⟩ := hr.rep.mem.1 hw
    exact (hr.good w' hw').1 _ _ ⟨s, hs1, a1, a2, b1, b2⟩ l1 l2
  · intro w hw; obtain ⟨w', hw', rfl⟩ := hr.rep.mem.1 hw
    exact (hr.good w' hw').2 _ _ ⟨s', hs2, c1, c2, d1, d2⟩ l3 l4
end sound
lemma hits_true {f : ℕ} {m : List ℕ} (h : hits f m = true) : ∃ e ∈ m, hit f e = true := by
  by_contra hc
  push Not at hc
  rw [hits_false fun e he => by simpa using hc e he] at h; simp at h
lemma app_mem {x y : List ℕ} {e : ℕ} : e ∈ app x y ↔ e ∈ x ∨ e ∈ y := by
  induction x with
  | nil => simp [app]
  | cons a x ih =>
    change e ∈ a :: app x y ↔ _
    simp only [List.mem_cons, ih, or_assoc]
def CmOk (F : W → ℕ) (r : List W) (col : ℕ → ℕ) (c : Cm) : Prop := ∃ κ ≤ 1, (∀ e ∈ c.a, ∃ w ∈ r, F w = e ∧ col w.s = κ) ∧
  ∀ e ∈ c.b, ∃ w ∈ r, F w = e ∧ col w.s = 1 - κ
lemma join_false {F : W → ℕ} {r : List W} {col : ℕ → ℕ} {k : List Cm → Bool} {w : W} (hw1 : col w.s ≤ 1)
    (hh : ∀ w' ∈ r, hit (F w) (F w') = true → col w.s ≠ col w'.s)
    (hk : ∀ cs, (∀ c ∈ cs, CmOk F (w :: r) col c) → k cs = false) : ∀ (cs : List Cm) (S O : List ℕ) (Q : List Cm),
    (∀ c ∈ cs, CmOk F r col c) → (∀ c ∈ Q, CmOk F (w :: r) col c) → (∀ e ∈ S, ∃ w' ∈ w :: r, F w' = e ∧ col w'.s = col w.s) →
    (∀ e ∈ O, ∃ w' ∈ w :: r, F w' = e ∧ col w'.s = 1 - col w.s) → join k (F w) cs S O Q = false := by
  intro cs
  induction cs with
  | nil =>
    intro S O Q _ hQ hS hO
    refine hk _ fun c hc => ?_
    simp only [List.mem_cons] at hc
    rcases hc with rfl | hc
    · exact ⟨col w.s, hw1, hS, hO⟩
    · exact hQ c hc
  | cons c cs ih =>
    intro S O Q hcs hQ hS hO
    have hc := hcs c (by simp)
    have hcs' : ∀ c ∈ cs, CmOk F r col c := fun c' h => hcs c' (by simp [h])
    obtain ⟨κ, hκ, ha, hb⟩ := hc
    have e : join k (F w) (c :: cs) S O Q = bif hits (F w) c.a then (bif hits (F w) c.b then true else join k (F w) cs (app c.b S) (app c.a O) Q)
        else (bif hits (F w) c.b then join k (F w) cs (app c.a S) (app c.b O) Q else join k (F w) cs S O (c :: Q)) := by
      change (Bool.rec (motive := fun _ => Bool)
        (Bool.rec (motive := fun _ => Bool) (join k (F w) cs S O (c :: Q)) (join k (F w) cs (app c.a S) (app c.b O) Q) (hits (F w) c.b))
        (Bool.rec (motive := fun _ => Bool) (join k (F w) cs (app c.b S) (app c.a O) Q) true (hits (F w) c.b)) (hits (F w) c.a) : Bool) = _
      rw [bR, bR, bR]
    rw [e]
    have hA : hits (F w) c.a = true → κ = 1 - col w.s := by
      intro h
      obtain ⟨x, hx, hhx⟩ := hits_true h
      obtain ⟨w', hw', e1, e2⟩ := ha x hx
      have := hh w' hw' (by rw [e1]; exact hhx)
      omega
    have hB : hits (F w) c.b = true → κ = col w.s := by
      intro h
      obtain ⟨x, hx, hhx⟩ := hits_true h
      obtain ⟨w', hw', e1, e2⟩ := hb x hx
      have := hh w' hw' (by rw [e1]; exact hhx)
      omega
    have up : ∀ {κ' : ℕ} {L : List ℕ}, (∀ e ∈ L, ∃ w' ∈ r, F w' = e ∧ col w'.s = κ') → ∀ e ∈ L, ∃ w' ∈ w :: r, F w' = e ∧ col w'.s = κ' := by
      intro κ' L h e he
      obtain ⟨w', h1, h2⟩ := h e he
      exact ⟨w', by simp [h1], h2⟩
    cases h1 : hits (F w) c.a with
    | true =>
      have k1 := hA h1
      cases h2 : hits (F w) c.b with
      | true => have k2 := hB h2; omega
      | false =>
        simp only [cond_true, cond_false]
        refine ih _ _ _ hcs' hQ ?_ ?_
        · intro e he
          rcases app_mem.1 he with h | h
          · obtain ⟨w', q1, q2, q3⟩ := up hb e h; exact ⟨w', q1, q2, by omega⟩
          · exact hS e h
        · intro e he
          rcases app_mem.1 he with h | h
          · obtain ⟨w', q1, q2, q3⟩ := up ha e h; exact ⟨w', q1, q2, by omega⟩
          · exact hO e h
    | false =>
      cases h2 : hits (F w) c.b with
      | true =>
        have k2 := hB h2
        simp only [cond_true, cond_false]
        refine ih _ _ _ hcs' hQ ?_ ?_
        · intro e he
          rcases app_mem.1 he with h | h
          · obtain ⟨w', q1, q2, q3⟩ := up ha e h; exact ⟨w', q1, q2, by omega⟩
          · exact hS e h
        · intro e he
          rcases app_mem.1 he with h | h
          · obtain ⟨w', q1, q2, q3⟩ := up hb e h; exact ⟨w', q1, q2, by omega⟩
          · exact hO e h
      | false =>
        simp only [cond_false]
        refine ih _ _ _ hcs' ?_ hS hO
        intro c' hc'
        simp only [List.mem_cons] at hc'
        rcases hc' with rfl | hc'
        · exact ⟨κ, hκ, up ha, up hb⟩
        · exact hQ c' hc'
lemma bip_aux {l o : ℕ} {col : ℕ → ℕ} : ∀ (v r : List W) (cs : List Cm), (∀ w ∈ v, col w.s ≤ 1) → (∀ c ∈ cs, CmOk (flag false l o) r col c) →
    (∀ w ∈ v, ∀ w' ∈ r, hit (flag false l o w) (flag false l o w') = true → col w.s ≠ col w'.s) →
    v.Pairwise (fun a b => hit (flag false l o b) (flag false l o a) = true → col b.s ≠ col a.s) → bip l o v cs = false := by
  intro v
  induction v with
  | nil => intros; rfl
  | cons w v ih =>
    intro r cs h1 h2 h3 h4
    rw [List.pairwise_cons] at h4
    change join (bip l o v) (flag false l o w) cs [flag false l o w] [] [] = false
    refine join_false (F := flag false l o) (h1 w (by simp)) (h3 w (by simp)) ?_ cs _ _ _ h2 (by simp) ?_ (by simp)
    · intro cs' hcs'
      refine ih (w :: r) cs' (fun x hx => h1 x (by simp [hx])) hcs' ?_ h4.2
      intro x hx w' hw'
      simp only [List.mem_cons] at hw'
      rcases hw' with rfl | hw'
      · exact h4.1 x hx
      · exact h3 x (by simp [hx]) w' hw'
    · intro e he
      simp only [List.mem_singleton] at he
      exact ⟨w, by simp, he.symm, rfl⟩
lemma anyE_false : ∀ {m : List ℕ}, m.Pairwise (fun p q => hit p q = false) → anyE m = false := by
  intro m
  induction m with
  | nil => intro _; rfl
  | cons f t ih =>
    intro h
    rw [List.pairwise_cons] at h
    change (Bool.rec (motive := fun _ => Bool) (anyE t) true (hits f t) : Bool) = false
    rw [bR, hits_false h.1, ih h.2]; rfl
lemma rmF_eq (F : W → ℕ) (f : ℕ) (t : List W) : rmF f (t.map F) = (t.eraseP (fun q => hit f (F q))).map F := by
  induction t with
  | nil => rfl
  | cons x t ih =>
    change (Bool.rec (motive := fun _ => List ℕ) (F x :: rmF f (t.map F)) (t.map F) (hit f (F x)) : List ℕ) = _
    rw [List.eraseP_cons]
    cases h : hit f (F x)
    · simp [ih]
    · simp
lemma eraseP_not {α : Type} {p : α → Bool} {a : α} : ∀ {t : List α}, t.Nodup → a ∈ t → p a = true → (∀ x ∈ t, p x = true → x = a) → a ∉ t.eraseP p := by
  intro t
  induction t with
  | nil => intro _ h; simp at h
  | cons x t ih =>
    intro hn ha hp hx
    rw [List.nodup_cons] at hn
    rw [List.eraseP_cons]
    cases h : p x
    · have hax : a ≠ x := fun e => by rw [← e, hp] at h; simp at h
      simp only [Bool.false_eq_true, if_false, List.mem_cons, not_or]
      simp only [List.mem_cons] at ha
      exact ⟨hax, ih hn.2 (ha.resolve_left hax) hp fun y hy => hx y (by simp [hy])⟩
    · have := hx x (by simp) h
      subst this
      simpa using hn.1
lemma star_false {F : W → ℕ} {a : W} : ∀ {v : List W}, v.Nodup → star (v.map F) = false →
    ∃ p q : W, [p, q].Sublist v ∧ hit (F p) (F q) = true ∧ p ≠ a ∧ q ≠ a := by
  intro v hn hst
  by_contra hno
  push Not at hno
  have bad : ∀ p q : W, [p, q].Sublist v → hit (F p) (F q) = true → p = a ∨ q = a := by
    intro p q h1 h2
    by_cases h : p = a
    · exact Or.inl h
    · exact Or.inr (hno p q h1 h2 h)
  clear hno
  have key : star (v.map F) = true := by
    clear hst
    induction v with
    | nil => rfl
    | cons w t ih =>
      rw [List.nodup_cons] at hn
      have bt : ∀ p q : W, [p, q].Sublist t → hit (F p) (F q) = true → p = a ∨ q = a := fun p q h => bad p q (h.cons w)
      have e : star ((w :: t).map F) = bif hits (F w) (t.map F) then (bif anyE (t.map F) then (bif hits (F w) (rmF (F w) (t.map F)) then false else
          (bif anyE (rmF (F w) (t.map F)) then false else true)) else true) else star (t.map F) := by
        change (Bool.rec (motive := fun _ => Bool) (star (t.map F)) (Bool.rec (motive := fun _ => Bool) true (Bool.rec (motive := fun _ => Bool)
          (Bool.rec (motive := fun _ => Bool) true false (anyE (rmF (F w) (t.map F)))) false (hits (F w) (rmF (F w) (t.map F)))) (anyE (t.map F))) (hits (F w) (t.map F)) : Bool) = _
        rw [bR, bR, bR, bR]
      rw [e]
      have edge : ∀ u : List W, u.Sublist t → a ∉ u → anyE (u.map F) = false := by
        intro u hu ha
        refine anyE_false ?_
        rw [List.pairwise_map, List.pairwise_iff_forall_sublist]
        intro p q hpq
        by_contra hc
        rw [Bool.not_eq_false] at hc
        have hm : ∀ x ∈ [p, q], x ∈ u := fun x hx => hpq.subset hx
        rcases bt p q (hpq.trans hu) hc with rfl | rfl
        · exact ha (hm p (by simp))
        · exact ha (hm q (by simp))
      cases h1 : hits (F w) (t.map F) with
      | false => rw [cond_false]; exact ih hn.2 bt
      | true =>
        rw [cond_true]
        have part : ∀ q ∈ t, hit (F w) (F q) = true → w = a ∨ q = a := fun q hq h => bad w q ((List.singleton_sublist.2 hq).cons_cons w) h
        by_cases hwa : w = a
        · subst hwa
          rw [edge t (List.Sublist.refl t) hn.1]; rfl
        · have pa : ∀ q ∈ t, hit (F w) (F q) = true → q = a := fun q hq h => (part q hq h).resolve_left hwa
          obtain ⟨x, hx, hhx⟩ := hits_true h1
          obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hx
          have hqa := pa q hq hhx
          subst hqa
          have hna : q ∉ t.eraseP (fun q => hit (F w) (F q)) := eraseP_not hn.2 hq hhx pa
          rw [rmF_eq, edge _ List.eraseP_sublist hna]
          have : hits (F w) ((t.eraseP (fun q => hit (F w) (F q))).map F) = false := by
            refine hits_false fun e he => ?_
            obtain ⟨y, hy, rfl⟩ := List.mem_map.1 he
            by_contra hc
            rw [Bool.not_eq_false] at hc
            have hyt : y ∈ t := List.eraseP_sublist.subset hy
            exact hna (pa y hyt hc ▸ hy)
          rw [this]
          cases anyE (t.map F) <;> rfl
  rw [key] at hst; simp at hst
lemma flk_eq (l o : ℕ) (v : List W) : ∀ k, flk l o v k = k (v.map (flag false l o)) := by
  induction v with
  | nil => intro k; rfl
  | cons w v ih =>
    intro k
    change flk l o v (fun r => k (flag false l o w :: r)) = _
    rw [ih]; rfl
def NK (R : ℕ → ℕ) (m T k' t : ℕ) (S : Finset ℕ) : Prop :=
  (∀ d a b S1 k0, k' = k0 + 1 → Bi R d a b S S1 → Live R m T k0 t S1 → S1.card < S.card) ∧
  ∀ a S1 k0 t0, k' = k0 + 1 → t = t0 + 1 → Un m a S S1 → Live R m T k0 t0 S1 → S1.card ≤ S.card
lemma Rep.nodup {v : List W} {S : Finset ℕ} (h : Rep v S) : v.Nodup := List.Nodup.of_map _ h.1
section sound
variable {P : List ℕ} {l m g T : ℕ} (X : Ctx P l m g T)
include X
lemma nk_ok {k k' t z : ℕ} {v : List W} {S : Finset ℕ} (hs : StOk P T l k z v S) (hm : Min R m T k' t S)
    (hx : k' ≤ S.card + t) (hst : flk l (wst (pos' t) l v) v star = false) : NK R m T k' t S := by
  rw [flk_eq] at hst
  have hsz := hm.size
  have av : ∀ a : ℕ, a ∈ S → ∃ p q : ℕ, p ∈ S ∧ q ∈ S ∧ p ≠ q ∧ p ≠ a ∧ q ≠ a ∧ Ht NN m T (pos' t) S p q := by
    intro a ha
    obtain ⟨wa, hwa, rfl⟩ := hs.rep.mem.1 ha
    obtain ⟨p, q, hpq, hh, h1, h2⟩ := star_false (F := flag false l (wst (pos' t) l v)) (a := wa) hs.rep.nodup hst
    have hp : p ∈ v := hpq.subset (by simp)
    have hq : q ∈ v := hpq.subset (by simp)
    have hne : p ≠ q := by
      have := hs.rep.nodup.sublist hpq
      simpa using this
    refine ⟨p.s, q.s, hs.rep.mem.2 ⟨p, hp, rfl⟩, hs.rep.mem.2 ⟨q, hq, rfl⟩, fun e => hne (hs.rep.inj hp hq e), fun e => h1 (hs.rep.inj hp hwa e),
      fun e => h2 (hs.rep.inj hq hwa e), hit_ht X hs hp hq hh⟩
  have he : ∀ t', pos' t = true ∨ t = t' → pos' t = true ∨ t' = 0 := by
    intro t' h
    rcases h with h | h
    · exact Or.inl h
    · subst h
      rcases Nat.eq_zero_or_pos t with h | h
      · exact Or.inr h
      · exact Or.inl (by simp [pos', h])
  have kb : ∀ d a b S1 k0, k' = k0 + 1 → Bi R d a b S S1 → Live R m T k0 t S1 → ∀ U, S = insert a (insert b U) → S1 = insert (op d a b) U → a ∈ U → b ∉ U → False := by
    rintro d a b S1 k0 rfl hb hl U rfl rfl ha hbU
    have hab := hb.1
    have hfS : op d a b ∉ insert a (insert b U) := fun h => hb.fresh hl hm.2 (sub_C _ _ (by simpa using h))
    have hf : op d a b ∉ U := fun h => hfS (by simp [h])
    have eS : insert a (insert b U) = insert b U := Finset.insert_eq_of_mem (by simp [ha])
    obtain ⟨x, f, h1, h2, h3⟩ := chrom (N := NN) (e := pos' t) hl (hb.min hl hm.2).2 (he t (Or.inr rfl))
    rw [Finset.card_insert_of_notMem hf] at h1
    rw [eS, Finset.card_insert_of_notMem hbU] at hx
    obtain ⟨p, q, hp, hq, hpq, hpa, hqa, hh⟩ := av a (by simp)
    have := ht_bi hab (Or.inr rfl) hl hp hq (fun e => absurd e hpa) (fun _ => hbU) (fun e => absurd e hqa) (fun _ => hbU) hh
    have m1 := phi_mem (g := op d a b) hp
    have m2 := phi_mem (g := op d a b) hq
    have hne : (if p = a ∨ p = b then op d a b else p) ≠ (if q = a ∨ q = b then op d a b else q) := by
      simp only [hpa, hqa, false_or]
      have h1' : p = b ∨ p ∈ U := by simp at hp; tauto
      have h2' : q = b ∨ q ∈ U := by simp at hq; tauto
      split_ifs with r s s
      · exact absurd (r.trans s.symm) hpq
      · intro e; exact hf (e ▸ h2'.resolve_left s)
      · intro e; exact hf (e ▸ h1'.resolve_left r)
      · exact hpq
    have k1 := h3 _ m1 _ m2 hne this
    have c1 := h2 _ m1; have c2 := h2 _ m2
    omega
  constructor
  · intro d a b S1 k0 hk' hb hl
    by_contra hc
    obtain ⟨hab, U, e1, e2, hal⟩ := id hb
    have hfS : op d a b ∉ S := fun h => hb.fresh hl (by rw [← hk']; exact hm.2) (sub_C _ _ (by simpa using h))
    have hf : op d a b ∉ U := fun h => hfS (by rw [e1]; simp [h])
    have hs1 := (hb.min hl (by rw [← hk']; exact hm.2)).size.1
    have hcS1 : S1.card = U.card + 1 := by rw [e2, Finset.card_insert_of_notMem hf]
    by_cases ha : a ∈ U
    · by_cases hbU : b ∈ U
      · have : S = U := by rw [e1, Finset.insert_eq_of_mem hbU, Finset.insert_eq_of_mem ha]
        rw [this] at hx; omega
      · exact kb d a b S1 k0 hk' hb hl U e1 e2 ha hbU
    · by_cases hbU : b ∈ U
      · exact kb d b a S1 k0 hk' hb.symm hl U (by rw [e1, Finset.insert_comm]) (by rw [e2, op_comm]) hbU ha
      · have : S.card = U.card + 2 := by
          rw [e1, Finset.card_insert_of_notMem (by simp [hab, ha]), Finset.card_insert_of_notMem hbU]
        omega
  · rintro a S1 k0 t0 rfl rfl hu hl
    by_contra hc
    obtain ⟨U, rfl, rfl⟩ := id hu
    have hf : a ^^^ m ∉ U := fun h => hu.fresh hl hm.2 (sub_C _ _ (by simp [h]))
    have ha : a ∈ U := by
      by_contra ha
      rw [Finset.card_insert_of_notMem hf, Finset.card_insert_of_notMem ha] at hc; omega
    have eS : insert a U = U := Finset.insert_eq_of_mem ha
    obtain ⟨x, f, h1, h2, h3⟩ := chrom (N := NN) (e := true) hl (hu.min hl hm.2).2 (Or.inl rfl)
    rw [Finset.card_insert_of_notMem hf] at h1
    rw [eS] at hx
    obtain ⟨p, q, hp, hq, hpq, hpa, hqa, hh⟩ := av a (by simp)
    have hpos : pos' (t0 + 1) = true := by simp [pos']
    rw [hpos] at hh
    have := ht_un hp hq (fun e => absurd e hpa) (fun e => absurd e hqa) hh
    simp only [hpa, hqa, if_false] at this
    have m1 : p ∈ insert (a ^^^ m) U := by rw [eS] at hp; simp [hp]
    have m2 : q ∈ insert (a ^^^ m) U := by rw [eS] at hq; simp [hq]
    have k1 := h3 _ m1 _ m2 hpq this
    have c1 := h2 _ m1; have c2 := h2 _ m2
    omega
lemma tst_sound {k k' t z : ℕ} {v : List W} {S : Finset ℕ} (hs : StOk P T l k z v S) (hm : Min R m T k' t S) (hk : k' ≤ k) :
    ∃ y, (∀ F : ℕ → Bool, tst (pos' t) l (k + 1 - t) v F = F y) ∧ (y = 0 ∨ (y = 1 ∧ v.length + t = k ∧ NK R m T k' t S)) := by
  have hsz := hm.size
  have hcard := hs.rep.card
  have e : ∀ F : ℕ → Bool, tst (pos' t) l (k + 1 - t) v F = bif Nat.beq v.length (k + 1 - t) then (bif rect (pos' t) l (wst (pos' t) l v) v [] then false else F 0) else
      (bif Nat.beq (v.length + 1) (k + 1 - t) then (bif bip l (wst (pos' t) l v) v [] then false else
        (bif flk l (wst (pos' t) l v) v star then F 0 else F 1)) else F 0) := by
    intro F
    change (Bool.rec (motive := fun _ => Bool)
      (Bool.rec (motive := fun _ => Bool) (F 0) (Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) (F 1) (F 0) (flk l (wst (pos' t) l v) v star)) false
        (bip l (wst (pos' t) l v) v [])) (Nat.beq (v.length + 1) (k + 1 - t)))
      (Bool.rec (motive := fun _ => Bool) (F 0) false (rect (pos' t) l (wst (pos' t) l v) v [])) (Nat.beq v.length (k + 1 - t)) : Bool) = _
    rw [bR, bR, bR, bR, bR]
  cases h1 : Nat.beq v.length (k + 1 - t) with
  | true =>
    have h1' := Nat.eq_of_beq_eq_true h1
    have hr := rect_ok X hs hm hk (by omega)
    exact ⟨0, fun F => by rw [e, h1, hr]; rfl, Or.inl rfl⟩
  | false =>
    cases h2 : Nat.beq (v.length + 1) (k + 1 - t) with
    | false => exact ⟨0, fun F => by rw [e, h1, h2]; rfl, Or.inl rfl⟩
    | true =>
      have h2' := Nat.eq_of_beq_eq_true h2
      have hbip : bip l (wst (pos' t) l v) v [] = false := by
        obtain ⟨x, f, q1, q2, q3⟩ := chrom (N := NN) (e := pos' t) hm.1 hm.2 (by
          rcases Nat.eq_zero_or_pos t with h | h
          · exact Or.inr h
          · exact Or.inl (by simp [pos', h]))
        refine bip_aux (col := f) v [] [] ?_ (by simp) (by simp) ?_
        · intro w hw
          have := q2 w.s (hs.rep.mem.2 ⟨w, hw, rfl⟩); omega
        · have hnd : v.Pairwise (fun a b => a.s ≠ b.s) := List.pairwise_map.1 hs.rep.1
          refine hnd.imp_of_mem fun {a b} ha hb hab hh => ?_
          exact q3 b.s (hs.rep.mem.2 ⟨b, hb, rfl⟩) a.s (hs.rep.mem.2 ⟨a, ha, rfl⟩) (Ne.symm hab) (hit_ht X hs hb ha hh)
      cases h3 : flk l (wst (pos' t) l v) v star with
      | true => exact ⟨0, fun F => by rw [e, h1, h2, hbip, h3]; rfl, Or.inl rfl⟩
      | false => exact ⟨1, fun F => by rw [e, h1, h2, hbip, h3]; rfl, Or.inr ⟨rfl, by omega, nk_ok X hs hm (by omega) h3⟩⟩
lemma cv_ok {t k k' z : ℕ} {v : List W} {S : Finset ℕ} {b : Bool} (hs : StOk P T l k z v S) (hl : Live R m T k' t S)
    (h : cv (pos' t) l v b = false) : b = false := by
  have hcov : Nat.beq (cov (pos' t) l v) l = true := by
    rw [Nat.beq_eq]
    apply Nat.eq_of_testBit_eq; intro i
    cases hli : l.testBit i with
    | false =>
      by_contra hc
      obtain ⟨w, _, hw⟩ := (cov_bit _ _ _ _).1 (by simpa using hc)
      rw [sp_bit, hli] at hw; simp at hw
    | true =>
      rw [cov_bit]
      obtain ⟨⟨m1, m2, t1, t2⟩, _⟩ := X.lg i hli
      obtain ⟨w, hw, hs1⟩ := hl.cov m1 m2 t1 t2
      obtain ⟨w', hw', rfl⟩ := hs.rep.mem.1 hw
      exact ⟨w', hw', by rw [sp_bit, hli, hs1]; rfl⟩
  simp only [cv, bR, hcov, cond_true] at h
  cases hp : pos' t <;> rw [hp] at h <;> simpa using h
end sound
section sound
variable {P : List ℕ} {l m g T : ℕ} (X : Ctx P l m g T)
include X
lemma gate_sound {f : ℕ → List W → Bool} {d : Bool} {e n z t k k' : ℕ} {v : List W} {S S' : Finset ℕ} {a c : W} {d' : Bool}
    (hs : StOk P T l (k + 1) z v S) (hm : Min R m T (k' + 1) t S) (hk : k' ≤ k) (hd : d = pos' t) (hn : n = v.length)
    (hSe : S'.card ≤ e) (hb : Bi R d' a.s c.s S S') (hl : Live R m T k' t S') (ha : a ∈ v) (hc : c ∈ v)
    (hp : pair (modeF n e (mid f m g e (Nat.pred n) z v)) (mkx d l (wst d l v) a) (mkx d l (wst d l v) c) = false) :
    ∃ z' r, f z' r = false ∧ StOk P T l k z' r S' ∧ ∀ w ∈ r, w = opW d' a c ∨ w ∈ v := by
  subst hd hn
  have hmin := hb.min hl hm.2
  have hpos := hl.pos
  have hfr := hb.fresh hl hm.2
  have hosS : ∀ w ∈ v, w.s ≠ (opW d' a c).s := fun w hw e => hfr (by
    rw [← opW_s, ← e]; exact sub_C _ _ (by simpa using hs.rep.mem.2 ⟨w, hw, rfl⟩))
  have ho0 : (opW d' a c).s ≠ 0 := fun e => hfr (by rw [← opW_s, e]; simp [C])
  have ho1 : (opW d' a c).s ≠ m := fun e => hfr (by rw [← opW_s, e]; simp [C])
  obtain ⟨r0, hr0, hins⟩ := ins_spec (opW d' a c) v hosS
  obtain ⟨s1, s2, s3, s4⟩ := shape_all hosS hr0 hs.rep.1 ha hc hb.1
  have hp := pair_false hp d'
  generalize hoa : dfc (pos' t) d' l (wst (pos' t) l v) a c = da at hp
  generalize hoc : dfc (pos' t) d' l (wst (pos' t) l v) c a = dc at hp
  have filt : ∀ {x y : W}, (∀ i, (Nat.land (sp (pos' t) l x.s) (wst (pos' t) l v)).testBit i = true → bif d' then y.s.testBit (NN + i) = false else y.s.testBit i = true) →
      dfc (pos' t) d' l (wst (pos' t) l v) x y = 0 := by
    intro x y hu
    unfold dfc
    generalize Nat.land (sp (pos' t) l x.s) (wst (pos' t) l v) = u at *
    cases d'
    · simp only [Bool.cond_false, nl, nx] at hu ⊢
      apply Nat.eq_of_testBit_eq; intro i
      have := hu i
      rw [Nat.testBit_xor, Nat.testBit_and]; cases h1 : u.testBit i <;> simp_all
    · simp only [Bool.cond_true, nl, nsr] at hu ⊢
      apply Nat.eq_of_testBit_eq; intro i
      have := hu i
      rw [Nat.testBit_and, Nat.testBit_shiftRight]; cases h1 : u.testBit i <;> simp_all
  have fa : a.s ∉ S' → da = 0 := fun h => by
    rw [← hoa]; exact filt fun i hi => drop_ok X hs.rep hb hl ha h hi
  have fc : c.s ∉ S' → dc = 0 := fun h => by
    rw [← hoc]; exact filt fun i hi => drop_ok X hs.rep hb.symm hl hc h hi
  have b0 : ∀ {q : ℕ}, q = 0 → Nat.beq q 0 = true := fun h => by rw [h]; rfl
  have hput : ∀ h, put m (opW d' a c).s (opW d' a c).a (opW d' a c).b v h = h r0 := fun h => by
    rw [put_eq (by cases d' <;> rfl) (by cases d' <;> rfl) ho0 ho1, hins]
  have hv2 : 2 ≤ v.length := by
    rw [← hs.rep.card]
    have : ({a.s, c.s} : Finset ℕ) ⊆ S := by
      intro x hx; simp at hx; rcases hx with rfl | rfl; exacts [hb.sub.1, hb.sub.2.1]
    have h2 := Finset.card_le_card this
    rwa [Finset.card_pair hb.1] at h2
  have hpr : Nat.pred v.length + 1 = v.length := by simp [Nat.pred_eq_sub_one]; omega
  have main : ∀ {ka kc : Bool} {r : List W}, ka = decide (a.s ∈ S') → kc = decide (c.s ∈ S') → Shape (opW d' a c) a c v ka kc r →
      r.length = S'.card ∧ StOk P T l k (z + (a.c &&& c.c) - (opW d' a c).c - (bif ka then a.c else 0) - (bif kc then c.c else 0)) r S' ∧
      ∀ w ∈ r, w = opW d' a c ∨ w ∈ v := by
    intro ka kc r h1 h2 h3
    have := (bi_st X hs hm hk hb hl ha hc h1 h2 h3).1
    exact ⟨this.rep.card.symm, this, fun w hw => h3.mem hw⟩
  have hguard : Nat.beq (Nat.land (z + (a.c &&& c.c) - (opW d' a c).c) g) g = true := by
    by_cases q1 : a.s ∈ S' <;> by_cases q2 : c.s ∈ S'
    · exact (bi_st X hs hm hk hb hl ha hc (by simp [q1]) (by simp [q2]) s4).2
    · exact (bi_st X hs hm hk hb hl ha hc (by simp [q1]) (by simp [q2]) s2).2
    · exact (bi_st X hs hm hk hb hl ha hc (by simp [q1]) (by simp [q2]) s3).2
    · exact (bi_st X hs hm hk hb hl ha hc (by simp [q1]) (by simp [q2]) s1).2
  have fin : ∀ {z' : ℕ} {r : List W} {mk : (List W → Bool) → Bool}, (∀ h, mk h = h r) → StOk P T l k z' r S' → (∀ w ∈ r, w = opW d' a c ∨ w ∈ v) →
      child f g mk z' = false → ∃ z' r, f z' r = false ∧ StOk P T l k z' r S' ∧ ∀ w ∈ r, w = opW d' a c ∨ w ∈ v :=
    fun {z' r mk} h1 h2 h3 h4 => ⟨z', r, child_sound X h1 h2 hmin hk h4, h2, h3⟩
  by_cases q1 : a.s ∈ S' <;> by_cases q2 : c.s ∈ S'
  · obtain ⟨c1, c3, c4⟩ := main (by simp [q1]) (by simp [q2]) s4
    have hlen := s4.len; simp at hlen
    have hmid := mid_false (modeF_false hp (fun h => by omega) (fun h => by omega)) hguard
    exact fin hput c3 c4 ((kids_false hmid).2.2.2 (by omega))
  · obtain ⟨c1, c3, c4⟩ := main (by simp [q1]) (by simp [q2]) s2
    have hlen := s2.len; simp only [Bool.cond_true, Bool.cond_false] at hlen
    have hmid := mid_false (modeF_false hp (fun h => by omega) (fun h => Or.inr (fc q2))) hguard
    exact fin (fun h => by rw [hput, rm_eq]) (by simpa using c3) c4 ((kids_false hmid).2.1 (b0 (fc q2)) (by omega))
  · obtain ⟨c1, c3, c4⟩ := main (by simp [q1]) (by simp [q2]) s3
    have hlen := s3.len; simp only [Bool.cond_true, Bool.cond_false] at hlen
    have hmid := mid_false (modeF_false hp (fun h => by omega) (fun h => Or.inl (fa q1))) hguard
    exact fin (fun h => by rw [hput, rm_eq]) (by simpa using c3) c4 ((kids_false hmid).2.2.1 (b0 (fa q1)) (by omega))
  · obtain ⟨c1, c3, c4⟩ := main (by simp [q1]) (by simp [q2]) s1
    have hlen := s1.len; simp only [Bool.cond_false] at hlen
    have hmid := mid_false (modeF_false hp (fun h => ⟨fa q1, fc q2⟩) (fun h => Or.inl (fa q1))) hguard
    exact fin (fun h => by rw [hput, rm_eq]) (by simpa using c3) c4 ((kids_false hmid).1 (b0 (fa q1)) (b0 (fc q2)))
end sound
def notW (m : ℕ) (a : W) : W := ⟨a.s ^^^ m, a.b, a.a, a.c, 0⟩
section sound
variable {P : List ℕ} {l m g T : ℕ} (X : Ctx P l m g T)
include X
lemma un_st {k k' t z : ℕ} {v r : List W} {S S' : Finset ℕ} {a : W} {ka : Bool}
    (hs : StOk P T l (k + 1) z v S) (hm : Min R m T (k' + 1) (t + 1) S) (hk : k' ≤ k) (hb : Un m a.s S S')
    (hl : Live R m T k' t S') (ha : a ∈ v) (hka : ka = decide (a.s ∈ S'))
    (hsh : bif ka then r.Perm (notW m a :: v) else (a :: r).Perm (notW m a :: v)) :
    StOk P T l k (z - a.c - (bif ka then a.c else 0)) r S' := by
  obtain ⟨b, hb15, hcl, hz⟩ := hs.bud
  have hle := cnt_le X hs.rep hs.wok hcl hm (by omega)
  have hfr := hb.fresh hl hm.2
  have hfS : a.s ^^^ m ∉ S := fun h => hfr (sub_C _ _ (by simpa using h))
  have wa := hs.wok a ha
  have haS : a.s ∈ S := hb.sub.1
  have wo : WOk P (notW m a) := by
    refine ⟨wa.pb, wa.pa, by rw [Nat.or_comm]; exact wa.ec, fun j hj h => ?_, fun j hj h => ?_⟩
    · change (a.s ^^^ m) &&& _ = _
      rw [and_neg (X.hP j hj).1, wa.cb j hj h]; simp
    · change (a.s ^^^ m) &&& _ = _
      rw [and_neg (X.hP j hj).1, wa.ca j hj h]; simp
  have hov : ((notW m a :: v).map W.s).Nodup := by
    simp only [List.map_cons, List.nodup_cons]
    refine ⟨fun hm => hfS ?_, hs.rep.1⟩
    rw [← hs.rep.2]; simpa [notW] using hm
  have hov2 : ∀ x, x ∈ (notW m a :: v).map W.s ↔ x = a.s ^^^ m ∨ x ∈ S := fun x => by
    rw [← hs.rep.2]; simp [notW]
  have hS' : ∀ x, x ∈ S' ↔ x = a.s ^^^ m ∨ (x ∈ S ∧ (x = a.s → ka = true)) := by
    intro x
    obtain ⟨U, e1, e2⟩ := hb
    rw [e2, Finset.mem_insert]
    constructor
    · rintro (h | h)
      · exact Or.inl h
      · refine Or.inr ⟨by rw [e1]; simp [h], ?_⟩
        rintro rfl; rw [hka, e2]; simp [h]
    · rintro (h | ⟨h, f1⟩)
      · exact Or.inl h
      · rw [e1] at h; simp only [Finset.mem_insert] at h
        rcases h with h | h
        · have := f1 h; rw [hka, decide_eq_true_eq, e2, Finset.mem_insert] at this; rw [h]; exact this
        · exact Or.inr h
  have hne : a.s ≠ a.s ^^^ m := fun e => hfS (e ▸ haS)
  have hrep : Rep r S' := by
    cases hkk : ka with
    | true =>
      rw [hkk] at hsh hS'
      have hn := (hsh.map W.s).nodup_iff.2 hov
      refine ⟨hn, Finset.ext fun x => ?_⟩
      rw [List.mem_toFinset, (hsh.map W.s).mem_iff, hov2, hS']; simp
    | false =>
      rw [hkk] at hsh hS'
      have hn := (hsh.map W.s).nodup_iff.2 hov
      simp only [List.map_cons, List.nodup_cons] at hn
      refine ⟨hn.2, Finset.ext fun x => ?_⟩
      have hx := (hsh.map W.s).mem_iff (a := x)
      rw [hov2] at hx; simp only [List.map_cons, List.mem_cons] at hx
      rw [List.mem_toFinset, hS']
      constructor
      · intro h1
        rcases hx.1 (Or.inr h1) with e | e
        · exact Or.inl e
        · exact Or.inr ⟨e, fun e => absurd (e ▸ h1) hn.1⟩
      · rintro (e | ⟨e, f1⟩)
        · exact (hx.2 (Or.inl e)).resolve_left fun e' => hne (e'.symm.trans e)
        · exact (hx.2 (Or.inr e)).resolve_left fun e' => by simpa using f1 e'
  have hmem : ∀ w ∈ r, w = notW m a ∨ w ∈ v := by
    intro w hw
    have : w ∈ notW m a :: v := by
      cases hkk : ka <;> rw [hkk] at hsh
      · exact List.Perm.subset hsh (by simp [hw])
      · exact List.Perm.subset hsh hw
    simpa using this
  have hcnt : ∀ j, cnt r j + (bif ka then 0 else fl a j) = fl a j + cnt v j := by
    intro j
    have ef : fl (notW m a) j = fl a j := rfl
    cases hkk : ka <;> rw [hkk] at hsh
    · have := cnt_perm hsh j; simp only [cnt_cons, ef] at this; simp; omega
    · have := cnt_perm hsh j; simp only [cnt_cons, ef] at this; simp; omega
  have hwok : ∀ w ∈ r, WOk P w := fun w hw => (hmem w hw).elim (fun e => e ▸ wo) (hs.wok w)
  have hgood : ∀ w ∈ r, Good l w.s := fun w hw => by
    rcases hmem w hw with rfl | h
    · have hg := hs.good a ha
      refine ⟨fun i j h h1 h2 => ?_, fun i j h h1 h2 => ?_⟩
      · change (a.s ^^^ m).testBit i = (a.s ^^^ m).testBit j
        rw [Nat.testBit_xor, Nat.testBit_xor, hg.1 i j h h1 h2, (X.lg i h1).1.1, (X.lg j h2).1.1]
      · change (a.s ^^^ m).testBit (NN + i) = (a.s ^^^ m).testBit (NN + j)
        rw [Nat.testBit_xor, Nat.testBit_xor, hg.2 i j h h1 h2, (X.lg i h1).1.2.1, (X.lg j h2).1.2.1]
    · exact hs.good w h
  let b' : ℕ → ℕ := fun j => b j - fl a j
  have hcl' : Cl P T k b' S' := by
    intro j hj q hq hsol
    have hl1 := hle j hj
    have h2 := cnt_one ha hs.rep.1 j
    simp only [b'] at hq
    by_cases hkill : a.c.testBit (5 * j) = true
    · refine hcl j hj q ?_ (hb.kill (X.hP j hj).1 (wa.cst hj hkill) hsol)
      have : fl a j = 1 := by simp [fl, hkill]
      omega
    · refine hcl j hj (q + 1) ?_ (hb.im (X.hP j hj).1 hsol)
      have e1 : fl a j = 0 := by simp [fl, hkill]
      omega
  have hle' := cnt_le X hrep hwok hcl' (hb.min hl hm.2) hk
  refine ⟨hrep, hwok, hgood, b', fun j hj => ?_, hcl', ?_⟩
  · have := hb15 j hj; simp only [b']; omega
  · have ea : (bif ka then a.c else 0) = pk P.length (fun j => bif ka then fl a j else 0) := by
      cases ka
      · simp [pk]
      · exact fl_pk wa
    have le1 : ∀ j, (bif ka then fl a j else 0) ≤ 1 := fun j => by cases ka <;> simp [fl_le]
    rw [ea, hz]
    conv_lhs => rw [fl_pk wa]
    rw [pk_sub, pk_sub]
    · refine pk_congr fun j hj => ?_
      have q1 := hle j hj; have q2 := hle' j hj; have q3 := cnt_one ha hs.rep.1 j; have q4 := hb15 j hj
      have q5 := hcnt j; have q6 := fl_le a j
      simp only [b'] at q2 ⊢
      cases ka <;> simp at q5 ⊢ <;> omega
    · intro j hj; have := hle j hj; have := le1 j; have := fl_le a j; omega
    · intro j hj; have := hle j hj; have := fl_le a j; omega
end sound
lemma nots_false {f : ℕ → ℕ → List W → Bool} {m g e n z q : ℕ} {v r : List W} (h : nots f m g e n z q v r = false)
    {a : W} (ha : a ∈ r) (hq : a.s + 1 ≠ q) : ins (notW m a) v (fun v =>
      (bif (bif Nat.ble n e then child (f (a.s ^^^ m)) g (rm a.s a.s v) (z - a.c) else false) then true else
      (bif Nat.ble (n + 1) e then child (f (a.s ^^^ m)) g (fun h => h v) (z - a.c - a.c) else false))) = false := by
  induction r with
  | nil => simp at ha
  | cons w r ih =>
    change (Bool.rec (motive := fun _ => Bool) (nots f m g e n z q v r) true (Bool.rec (motive := fun _ => Bool)
      (st (Nat.xor w.s m) (fun s => st (Nat.sub z w.c) (fun z => ins ⟨s, w.b, w.a, w.c, 0⟩ v (fun v =>
        Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) false
          (child (f s) g (fun h => h v) (Nat.sub z w.c)) (Nat.ble (Nat.succ n) e)) true
          (Bool.rec (motive := fun _ => Bool) false (child (f s) g (rm w.s w.s v) z) (Nat.ble n e)))))) false (Nat.beq (Nat.succ w.s) q)) : Bool) = false at h
    rw [bR, bR] at h
    simp only [st_eq, bR] at h
    simp only [List.mem_cons] at ha
    rcases ha with rfl | ha
    · rw [Bool.eq_false_iff.2 fun h => hq (Nat.eq_of_beq_eq_true h), Bool.cond_false] at h
      cases hh : ins (notW m a) v (fun v =>
        (bif (bif Nat.ble n e then child (f (a.s ^^^ m)) g (rm a.s a.s v) (z - a.c) else false) then true else
        (bif Nat.ble (n + 1) e then child (f (a.s ^^^ m)) g (fun h => h v) (z - a.c - a.c) else false))) with
      | false => rfl
      | true =>
        have h : (bif ins (notW m a) v (fun v =>
          (bif (bif Nat.ble n e then child (f (a.s ^^^ m)) g (rm a.s a.s v) (z - a.c) else false) then true else
          (bif Nat.ble (n + 1) e then child (f (a.s ^^^ m)) g (fun h => h v) (z - a.c - a.c) else false))) then true
          else nots f m g e n z q v r) = false := h
        rw [hh] at h; simp at h
    · refine ih ?_ ha
      revert h
      cases nots f m g e n z q v r <;> simp
section sound
variable {P : List ℕ} {l m g T : ℕ} (X : Ctx P l m g T)
include X
lemma nots_sound {f : ℕ → ℕ → List W → Bool} {e n z q t k k' : ℕ} {v : List W} {S S' : Finset ℕ} {a : W}
    (hs : StOk P T l (k + 1) z v S) (hm : Min R m T (k' + 1) (t + 1) S) (hk : k' ≤ k) (hn : n = v.length)
    (hSe : S'.card ≤ e) (hb : Un m a.s S S') (hl : Live R m T k' t S') (ha : a ∈ v) (hq : a.s + 1 ≠ q) {rr : List W} (har' : a ∈ rr)
    (hp : nots f m g e n z q v rr = false) : ∃ z' r, f (a.s ^^^ m) z' r = false ∧ StOk P T l k z' r S' ∧ ∀ w ∈ r, w = notW m a ∨ w ∈ v := by
  subst hn
  have hmin := hb.min hl hm.2
  have hfr := hb.fresh hl hm.2
  have hosS : ∀ w ∈ v, w.s ≠ (notW m a).s := fun w hw e => hfr (by
    change a.s ^^^ m ∈ _
    have : w.s = a.s ^^^ m := e
    rw [← this]; exact sub_C _ _ (by simpa using hs.rep.mem.2 ⟨w, hw, rfl⟩))
  obtain ⟨r0, hr0, hins⟩ := ins_spec (notW m a) v hosS
  have h := nots_false hp har' hq
  rw [hins] at h
  have hl0 : r0.length = v.length + 1 := by rw [hr0.length_eq]; simp
  have hnd : (r0.map W.s).Nodup := by
    refine (hr0.map W.s).nodup_iff.2 ?_
    simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and]
    exact ⟨fun w hw => hosS w hw, hs.rep.1⟩
  have har : a ∈ r0 := hr0.symm.subset (by simp [ha])
  have hmem : ∀ w ∈ r0, w = notW m a ∨ w ∈ v := fun w hw => by simpa using hr0.subset hw
  by_cases q1 : a.s ∈ S'
  · have hst := un_st X hs hm hk hb hl ha (ka := true) (by simp [q1]) hr0
    have hc := hst.rep.card
    have hb1 : Nat.ble (v.length + 1) e = true := Nat.ble_eq_true_of_le (by omega)
    rw [hb1] at h
    have h : child (f (a.s ^^^ m)) g (fun h => h r0) (z - a.c - a.c) = false := by
      revert h; simp only [Bool.cond_true]
      cases child (f (a.s ^^^ m)) g (fun h => h r0) (z - a.c - a.c) <;> simp
    exact ⟨_, _, child_sound X (fun h => rfl) hst hmin hk h, hst, hmem⟩
  · have hperm : (a :: r0.filter (fun w => !(Nat.beq w.s a.s || Nat.beq w.s a.s))).Perm (notW m a :: v) := by
      rw [filter1]; exact (filter_perm hnd har).trans hr0
    have hst := un_st X hs hm hk hb hl ha (ka := false) (by simp [q1]) hperm
    simp only [Bool.cond_false, Nat.sub_zero] at hst
    have hc := hst.rep.card
    have hlen := hperm.length_eq
    simp only [List.length_cons] at hlen
    have hb1 : Nat.ble v.length e = true := Nat.ble_eq_true_of_le (by omega)
    rw [hb1] at h
    have h : child (f (a.s ^^^ m)) g (rm a.s a.s r0) (z - a.c) = false := by
      revert h; simp only [Bool.cond_true]
      cases child (f (a.s ^^^ m)) g (rm a.s a.s r0) (z - a.c) <;> simp
    exact ⟨_, _, child_sound X (rm_eq _ _ _) hst hmin hk h, hst, fun w hw => hmem w (List.mem_of_mem_filter hw)⟩
end sound
lemma scan_false {p : X → Bool} {xs : List X} (h : scan p xs = false) : ∀ c ∈ xs, p c = false := by
  induction xs with
  | nil => simp
  | cons a r ih =>
    change (Bool.rec (motive := fun _ => Bool) (scan p r) true (p a) : Bool) = false at h
    rw [bR] at h
    intro c hc
    simp only [List.mem_cons] at hc
    rcases hc with rfl | hc
    · revert h; cases p c <;> simp
    · refine ih ?_ c hc
      revert h; cases scan p r <;> simp
lemma pairs_false {h : X → X → Bool} {xs : List X} (hp : pairs h xs = false) : xs.Pairwise (fun a c => h a c = false) := by
  induction xs with
  | nil => simp
  | cons a r ih =>
    change (Bool.rec (motive := fun _ => Bool) (pairs h r) true (scan (h a) r) : Bool) = false at hp
    rw [bR] at hp
    rw [List.pairwise_cons]
    constructor
    · apply scan_false; revert hp; cases scan (h a) r <;> simp
    · apply ih; revert hp; cases pairs h r <;> simp
lemma beq_f {x y : ℕ} (h : x ≠ y) : Nat.beq x y = false := Bool.eq_false_iff.2 fun h' => h (Nat.eq_of_beq_eq_true h')
lemma pairsP_false {h : X → X → Bool} {xs : List X} {q : ℕ} {a c : X} (hp : pairsP q h xs = false) (ha : a ∈ xs) (hq : a.s = q)
    (hc : c ∈ xs) (hcq : c.s ≠ q) : h a c = false := by
  have h1 := scan_false hp a ha
  simp only [bR] at h1
  rw [hq, Nat.beq_refl, Bool.cond_true] at h1
  have h2 := scan_false h1 c hc
  beta_reduce at h2
  rwa [beq_f hcq, Bool.cond_false] at h2
lemma pairsQ_false {h : X → X → Bool} {xs : List X} {q q' : ℕ} {a c : X} (hp : pairsQ q q' h xs = false) (ha : a ∈ xs) (hq : a.s = q)
    (hc : c ∈ xs) (hcq : c.s = q') : h a c = false := by
  have h1 := scan_false hp a ha
  simp only [bR] at h1
  rw [hq, Nat.beq_refl, Bool.cond_true] at h1
  have h2 := scan_false h1 c hc
  beta_reduce at h2
  rwa [hcq, Nat.beq_refl, Bool.cond_true] at h2
lemma pos_eq (t : ℕ) : pos t = pos' t := by cases t <;> simp [pos, pos']
lemma fr_mem {xs : List X} {a : X} (ha : a ∈ xs) (h : a.w.r = 0) : a ∈ fr xs := by
  induction xs with
  | nil => simp at ha
  | cons x xs ih =>
    change a ∈ Bool.rec (motive := fun _ => List X) (fr xs) (x :: fr xs) (Nat.beq x.w.r 0)
    simp only [List.mem_cons] at ha
    rcases ha with rfl | ha
    · rw [h]; simp
    · cases Nat.beq x.w.r 0
      · exact ih ha
      · exact List.mem_cons_of_mem _ (ih ha)
lemma fs_mem {xs : List X} {a : X} (ha : a ∈ xs) (h : a.w.r ≠ 0) : a ∈ fs xs := by
  induction xs with
  | nil => simp at ha
  | cons x xs ih =>
    change a ∈ Bool.rec (motive := fun _ => List X) (x :: fs xs) (fs xs) (Nat.beq x.w.r 0)
    simp only [List.mem_cons] at ha
    rcases ha with rfl | ha
    · rw [beq_f h]; simp
    · cases Nat.beq x.w.r 0
      · exact List.mem_cons_of_mem _ (ih ha)
      · exact ih ha
lemma pairs_any {h : X → X → Bool} {xs : List X} (hp : pairs h xs = false) {a c : X} (ha : a ∈ xs) (hc : c ∈ xs) (hne : a ≠ c) :
    h a c = false ∨ h c a = false := by
  have hpw := pairs_false hp
  have : Std.Symm (fun a c : L_meta_11040.X => h a c = false ∨ h c a = false) := ⟨fun a b h => h.symm⟩
  exact (hpw.imp (S := fun a c => h a c = false ∨ h c a = false) fun h => Or.inl h).forall ha hc hne
lemma pairsN_false {h : X → X → Bool} {xs : List X} (hp : pairsN h xs = false) {a c : X} (ha : a ∈ xs) (hc : c ∈ xs) (hne : a ≠ c)
    (hr : a.w.r = 0 ∨ c.w.r = 0) : h a c = false ∨ h c a = false := by
  simp only [pairsN, bR] at hp
  cases h1 : pairs h (fr xs) with
  | true => rw [h1] at hp; simp at hp
  | false =>
    rw [h1, cond_false] at hp
    by_cases hra : a.w.r = 0
    · by_cases hrc : c.w.r = 0
      · exact pairs_any h1 (fr_mem ha hra) (fr_mem hc hrc) hne
      · exact Or.inl (scan_false (scan_false hp a (fr_mem ha hra)) c (fs_mem hc hrc))
    · have hrc := hr.resolve_left hra
      exact Or.inr (scan_false (scan_false hp c (fr_mem hc hrc)) a (fs_mem ha hra))
def Cod (R : ℕ → ℕ) (v : List W) : Prop := ∀ w ∈ v, w.r = 0 ∨ w.r = R w.s
def RR (R : ℕ → ℕ) : Prop := ∀ d a b, R a ≠ 0 → R b ≠ 0 → ¬ Al R d a b
lemma opW_r (d : Bool) (a c : W) : (opW d a c).r = 0 := by cases d <;> rfl
lemma mv_false (F : ℕ → ℕ → ℕ → List W → Bool) (l m g k t z : ℕ) (v : List W) (y : ℕ) (h : mv F l m g k t z v y = false) :
    node (F (k - 1) t) (pos' t) l m g (k - t - y) v.length z v pairsN = false ∧
    ∀ s, t = s + 1 → nots (fun q z v => cv (pos' s) l v (tst (pos' s) l (k - s) v (fun y =>
      bif node (F (k - 2) s) (pos' s) l m g (k - 1 - s - y) v.length z v (pairsP q) then true
      else prd s (fun s => nots (fun q' z v => cv (pos' s) l v (tst (pos' s) l (k - 1 - s) v (fun y =>
        node (F (k - 3) s) (pos' s) l m g (k - 2 - s - y) v.length z v (pairsQ q q'))))
        m g (k - 1 - s - y) v.length z (q + 1) v v)))) m g (k - s - y) v.length z 0 v v = false := by
  change (Bool.rec (motive := fun _ => Bool) (prd t (fun s => nots (fun q z v => cv (pos s) l v (tst (pos s) l (k - s) v (fun y =>
      (Bool.rec (motive := fun _ => Bool) (prd s (fun s => nots (fun q' z v => cv (pos s) l v (tst (pos s) l (k - 1 - s) v (fun y =>
        node (F (k - 3) s) (pos s) l m g (k - 2 - s - y) v.length z v (pairsQ q q'))))
        m g (k - 1 - s - y) v.length z (q + 1) v v)) true
        (node (F (k - 2) s) (pos s) l m g (k - 1 - s - y) v.length z v (pairsP q)) : Bool)))) m g (k - s - y) v.length z 0 v v)) true
      (node (F (k - 1) t) (pos t) l m g (k - t - y) v.length z v pairsN) : Bool) = false at h
  simp only [bR, pos_eq] at h
  cases h1 : node (F (k - 1) t) (pos' t) l m g (k - t - y) v.length z v pairsN with
  | true => rw [h1] at h; simp at h
  | false =>
    rw [h1, Bool.cond_false] at h
    refine ⟨rfl, ?_⟩
    rintro s rfl
    exact h
lemma NK.sizeB {m T k k' t : ℕ} {S S1 : Finset ℕ} {d : Bool} {a b n y : ℕ} (hn : S.card = n) (hm : Min R m T (k' + 1) t S) (hk : k' + 1 ≤ k)
    (hb : Bi R d a b S S1) (hl : Live R m T k' t S1) (hy : y = 0 ∨ (y = 1 ∧ n + t = k ∧ NK R m T (k' + 1) t S)) : S1.card ≤ k - t - y := by
  have hs := (hb.min hl hm.2).size.1
  rcases hy with rfl | ⟨rfl, h1, h2⟩
  · omega
  · have := h2.1 d a b S1 k' rfl hb hl; omega
lemma NK.sizeU {m T k k' t : ℕ} {S S1 : Finset ℕ} {a n y : ℕ} (hn : S.card = n) (hm : Min R m T (k' + 1) (t + 1) S) (hk : k' + 1 ≤ k)
    (hb : Un m a S S1) (hl : Live R m T k' t S1) (hy : y = 0 ∨ (y = 1 ∧ n + (t + 1) = k ∧ NK R m T (k' + 1) (t + 1) S)) : S1.card ≤ k - t - y := by
  have hs := (hb.min hl hm.2).size.1
  rcases hy with rfl | ⟨rfl, h1, h2⟩
  · omega
  · have := h2.2 a S1 k' t rfl rfl hb hl; omega
section sound
variable {P : List ℕ} {l m g T : ℕ} (X : Ctx P l m g T)
include X
lemma node_bi {f : ℕ → List W → Bool} {d : Bool} {e n z t k k' : ℕ} {v : List W} {S S' : Finset ℕ} {x y : ℕ} {d' : Bool}
    {go : (L_meta_11040.X → L_meta_11040.X → Bool) → List L_meta_11040.X → Bool}
    (hs : StOk P T l (k + 1) z v S) (hm : Min R m T (k' + 1) t S) (hk : k' ≤ k) (hd : d = pos' t) (hn : n = v.length)
    (hSe : S'.card ≤ e) (hb : Bi R d' x y S S') (hl : Live R m T k' t S')
    (hgo : ∀ h xs, go h xs = false → ∀ a c : W, a ∈ v → c ∈ v → a.s = x → c.s = y → xs = v.map (mkx d l (wst d l v)) →
      h (mkx d l (wst d l v) a) (mkx d l (wst d l v) c) = false ∨ h (mkx d l (wst d l v) c) (mkx d l (wst d l v) a) = false)
    (hp : node f d l m g e n z v go = false) : ∃ z' r, f z' r = false ∧ StOk P T l k z' r S' ∧ ∀ w ∈ r, (w.s = op d' x y ∧ w.r = 0) ∨ w ∈ v := by
  rw [node_eq] at hp
  obtain ⟨a, ha, rfl⟩ := hs.rep.mem.1 hb.sub.1
  obtain ⟨c, hc, rfl⟩ := hs.rep.mem.1 hb.sub.2.1
  rcases hgo _ _ hp a c ha hc rfl rfl rfl with h | h
  · obtain ⟨z', r, h1, h2, h3⟩ := gate_sound X hs hm hk hd hn hSe hb hl ha hc h
    exact ⟨z', r, h1, h2, fun w hw => (h3 w hw).imp (fun e => ⟨by rw [e, opW_s], by rw [e, opW_r]⟩) id⟩
  · obtain ⟨z', r, h1, h2, h3⟩ := gate_sound X hs hm hk hd hn hSe hb.symm hl hc ha h
    exact ⟨z', r, h1, h2, fun w hw => (h3 w hw).imp (fun e => ⟨by rw [e, opW_s, op_comm], by rw [e, opW_r]⟩) id⟩
lemma mv_sound (hR : RR R) {F : ℕ → ℕ → ℕ → List W → Bool}
    (hF : ∀ (k t z : ℕ) (v : List W) (S : Finset ℕ), F k t z v = false → StOk P T l k z v S → Cod R v → ∀ k' ≤ k, ¬ Min R m T k' t S)
    {k t z y : ℕ} {v : List W} {S : Finset ℕ} (hs : StOk P T l k z v S) (hcod : Cod R v) (hlen : 2 ≤ v.length)
    (h : mv F l m g k t z v y = false) : ∀ k' ≤ k, Min R m T k' t S → (y = 0 ∨ (y = 1 ∧ v.length + t = k ∧ NK R m T k' t S)) → False := by
  intro k' hk hm hy
  obtain ⟨hA, hN⟩ := mv_false F l m g k t z v y h
  have hcard := hs.rep.card
  have codB : ∀ {v r : List W} {o : ℕ}, Cod R v → (∀ w ∈ r, (w.s = o ∧ w.r = 0) ∨ w ∈ v) → Cod R r := by
    intro v r o hv hr w hw
    rcases hr w hw with ⟨_, h⟩ | h
    · exact Or.inl h
    · exact hv w h
  have codU : ∀ {v r : List W} {a : W}, Cod R v → (∀ w ∈ r, w = notW m a ∨ w ∈ v) → Cod R r := by
    intro v r o hv hr w hw
    rcases hr w hw with h | h
    · exact Or.inl (by rw [h]; rfl)
    · exact hv w h
  rcases first_move k' t S hm (by omega) with
    ⟨k0, d, a, b, S1, rfl, hb, hl⟩ | ⟨k0, t0, a, d, c, S1, S2, rfl, rfl, hu, hb, hl⟩ |
    ⟨k0, t0, a, a', d, S1, S2, S3, rfl, rfl, hu, hne, hu', hb, hl⟩
  · obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    obtain ⟨z', r, hf, hst, hmem⟩ := node_bi X hs hm (by omega) rfl rfl (NK.sizeB hcard hm hk hb hl hy) hb hl (fun h xs hp a c ha hc hax hcy hxs => by
      subst hxs
      refine pairsN_false hp (List.mem_map_of_mem ha) (List.mem_map_of_mem hc) ?_ ?_
      · intro e
        have : a.s = c.s := congrArg L_meta_11040.X.s e
        exact hb.1 (by rw [← hax, ← hcy, this])
      · by_contra hc'
        push Not at hc'
        obtain ⟨_, U, _, _, hal⟩ := hb
        have h1 : a.r = R a.s := (hcod a ha).resolve_left hc'.1
        have h2 : c.r = R c.s := (hcod c hc).resolve_left hc'.2
        have g1 : a.r ≠ 0 := hc'.1
        have g2 : c.r ≠ 0 := hc'.2
        rw [← hax, ← hcy] at hal
        exact hR _ _ _ (by rw [← h1]; exact g1) (by rw [← h2]; exact g2) hal) hA
    exact hF _ _ _ _ _ hf hst (codB hcod hmem) k0 (by simpa using hk) (hb.min hl hm.2)
  · obtain ⟨k, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
    have hl1 := hb.live hl
    obtain ⟨wa, hwa, rfl⟩ := hs.rep.mem.1 hu.sub.1
    have h2 := hN t0 rfl
    obtain ⟨z1, r1, hf1, hst1, hmem1⟩ := nots_sound X (k := k + 1) hs hm (by omega) rfl (NK.sizeU hcard hm hk hu hl1 hy) hu hl1 hwa (by omega) hwa h2
    have hm1 := hu.min hl1 hm.2
    have hf1 := cv_ok X hst1 hl1 hf1
    obtain ⟨y1, hF1, hy1⟩ := tst_sound X hst1 hm1 (by omega)
    have hf1 := (hF1 _).symm.trans hf1
    beta_reduce at hf1
    rw [Bool.cond_eq_ite] at hf1
    split_ifs at hf1 with hf2
    rw [Bool.not_eq_true] at hf2
    obtain ⟨z', r, hf, hst, hmem⟩ := node_bi X hst1 hm1 (by omega) rfl rfl (NK.sizeB hst1.rep.card hm1 (by omega) hb hl hy1) hb hl (fun h xs hp a c ha hc hax hcy hxs => by
      subst hxs
      exact Or.inl (pairsP_false hp (List.mem_map_of_mem ha) hax (List.mem_map_of_mem hc) (fun e => hb.1 (by rw [← hcy, ← e]; rfl)))) hf2
    exact hF _ _ _ _ _ hf hst (codB (codU hcod hmem1) hmem) k0 (by simpa using hk) (hb.min hl hm1.2)
  · obtain ⟨k, rfl⟩ : ∃ j, k = j + 3 := ⟨k - 3, by omega⟩
    have hl1 := hb.live hl
    have hl2 := hu'.live hl1
    obtain ⟨wa, hwa, rfl⟩ := hs.rep.mem.1 hu.sub.1
    have h2 := hN (t0 + 1) rfl
    obtain ⟨z1, r1, hf1, hst1, hmem1⟩ := nots_sound X (k := k + 2) hs hm (by omega) rfl (NK.sizeU hcard hm hk hu hl2 hy) hu hl2 hwa (by omega) hwa h2
    have hm1 := hu.min hl2 hm.2
    have hf1 := cv_ok X hst1 hl2 hf1
    obtain ⟨y1, hF1, hy1⟩ := tst_sound X hst1 hm1 (by omega)
    have hf1 := (hF1 _).symm.trans hf1
    beta_reduce at hf1
    rw [Bool.cond_eq_ite] at hf1
    split_ifs at hf1 with hf2
    obtain ⟨wa', hwa', rfl⟩ := hst1.rep.mem.1 hu'.sub.1
    obtain ⟨z2, r2, hf3, hst2, hmem2⟩ := nots_sound X (k := k + 1) hst1 hm1 (by omega) rfl (NK.sizeU hst1.rep.card hm1 (by omega) hu' hl1 hy1) hu' hl1 hwa' (by omega) hwa' hf1
    have hm2 := hu'.min hl1 hm1.2
    have hf3 := cv_ok X hst2 hl1 hf3
    obtain ⟨y2, hF3, hy2⟩ := tst_sound X hst2 hm2 (by omega)
    have hf3 := (hF3 _).symm.trans hf3
    beta_reduce at hf3
    obtain ⟨z', r, hf, hst, hmem⟩ := node_bi X hst2 hm2 (by omega) rfl rfl (NK.sizeB hst2.rep.card hm2 (by omega) hb hl hy2) hb hl (fun h xs hp a c ha hc hax hcy hxs => by
      subst hxs
      exact Or.inl (pairsQ_false hp (List.mem_map_of_mem ha) hax (List.mem_map_of_mem hc) hcy)) hf3
    exact hF _ _ _ _ _ hf hst (codB (codU (codU hcod hmem1) hmem2) hmem) k0 (by simpa using hk) (hb.min hl hm2.2)
theorem look_sound (hR : RR R) : ∀ (fuel k t z : ℕ) (v : List W) (S : Finset ℕ), look l m g fuel k t z v = false → StOk P T l k z v S → Cod R v →
    ∀ k' ≤ k, ¬ Min R m T k' t S := by
  intro fuel
  induction fuel with
  | zero => intro k t z v S h; simp [look] at h
  | succ fuel ih =>
    intro k t z v S h hs hcod k' hk hm
    change (Bool.rec (motive := fun _ => Bool) (tst (pos t) l (k + 1 - t) v (fun y => mv (look l m g fuel) l m g k t z v y)) true (Nat.ble v.length 1) : Bool) = false at h
    rw [bR, pos_eq] at h
    cases h0 : Nat.ble v.length 1 with
    | true => rw [h0] at h; simp at h
    | false =>
      rw [h0, cond_false] at h
      have hlen : 2 ≤ v.length := by
        by_contra hc
        rw [Nat.ble_eq_true_of_le (by omega)] at h0; simp at h0
      obtain ⟨y, hFy, hyk⟩ := tst_sound X hs hm hk
      have hy := (hFy _).symm.trans h
      beta_reduce at hy
      exact mv_sound X hR ih hs hcod hlen hy k' hk hm hyk
end sound
lemma Live.W {m T k t : ℕ} {S : Finset ℕ} {Q : Set ℕ} (hl : Live R m T k t S) (hQ : (S : Set ℕ) ⊆ Q) : Sol Z0 m T k Q := hl.sol.mono le_rfl hQ
lemma front {m T : ℕ} (hR : ∀ d a b, (R a = 0 ∨ R b = 0) → Al R d a b) {k t : ℕ} {S : Finset ℕ} (hl : Live Z0 m T k t S)
    (hm : ∀ q < k, ¬ Sol Z0 m T q (C m ({x | R x ≠ 0} ∪ (S : Set ℕ)))) :
    Live R m T k t S ∨ ∃ k0 d a b S1, k = k0 + 1 ∧ R a ≠ 0 ∧ R b ≠ 0 ∧ Bi Z0 d a b S S1 ∧ Live Z0 m T k0 t S1 := by
  induction hl with
  | stop => exact Or.inl .stop
  | @un k t a U hl ih =>
    set Q : Set ℕ := {x | R x ≠ 0} with hQ
    have hfr : a ^^^ m ∉ C m (Q ∪ ((insert a U : Finset ℕ) : Set ℕ)) := by
      intro hg
      apply hm k (by omega)
      refine hl.sol.mono le_rfl fun x hx => ?_
      simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at hx
      rcases hx with rfl | hx
      · exact hg
      · exact Or.inl (Or.inr (by simp [hx]))
    have hfU : a ^^^ m ∉ U := fun h => hfr (Or.inl (Or.inr (by simp [h])))
    have hfR : R (a ^^^ m) = 0 := by
      by_contra h; exact hfr (Or.inl (Or.inl h))
    have hm' : ∀ q < k, ¬ Sol Z0 m T q (C m (Q ∪ ((insert (a ^^^ m) U : Finset ℕ) : Set ℕ))) := by
      intro q hq hs
      refine hm (q + 1) (by omega) (.un (a := a) (Or.inl (Or.inr (by simp))) (hs.mono le_rfl ?_))
      rintro x ((hx | hx) | hx)
      · exact Or.inr (Or.inl (Or.inl hx))
      · simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at hx
        rcases hx with rfl | hx
        · exact Or.inl rfl
        · exact Or.inr (Or.inl (Or.inr (by simp [hx])))
      · exact Or.inr (Or.inr hx)
    rcases ih hm' with h | ⟨k0, d, x, y, S1, rfl, hx, hy, ⟨hxy, V, e1, rfl, hal⟩, hl1⟩
    · exact Or.inl (.un h)
    · have nx : x ≠ a ^^^ m := fun e => hx (e ▸ hfR)
      have ny : y ≠ a ^^^ m := fun e => hy (e ▸ hfR)
      have hmV : a ^^^ m ∈ V := by
        have : a ^^^ m ∈ insert x (insert y V) := by rw [← e1]; simp
        simp at this
        rcases this with h | h | h
        · exact absurd h.symm nx
        · exact absurd h.symm ny
        · exact h
      have eU : U = insert x (insert y (V.erase (a ^^^ m))) := by
        ext z
        by_cases hz : z = a ^^^ m
        · subst hz
          simp [hfU, Ne.symm nx, Ne.symm ny]
        · have : z ∈ insert (a ^^^ m) U ↔ z ∈ insert x (insert y V) := by rw [e1]
          simp only [Finset.mem_insert, hz, false_or, Finset.mem_erase, ne_eq, not_false_eq_true, true_and] at this ⊢
          exact this
      refine Or.inr ⟨k0 + 1, d, x, y, insert a (insert (op d x y) (V.erase (a ^^^ m))), rfl, hx, hy,
        ⟨hxy, insert a (V.erase (a ^^^ m)), ?_, ?_, hal⟩, ?_⟩
      · rw [eU]; ext z; simp only [Finset.mem_insert]; tauto
      · ext z; simp only [Finset.mem_insert]; tauto
      · refine .un ?_
        have : insert (a ^^^ m) (insert (op d x y) (V.erase (a ^^^ m))) = insert (op d x y) V := by
          rw [Finset.insert_comm, Finset.insert_erase hmV]
        rw [this]; exact hl1
  | @bi k t d0 a b U hab hal0 hl ih =>
    set Q : Set ℕ := {x | R x ≠ 0} with hQ
    have hb0 : Bi Z0 d0 a b (insert a (insert b U)) (insert (op d0 a b) U) := ⟨hab, U, rfl, rfl, hal0⟩
    by_cases hW : R a ≠ 0 ∧ R b ≠ 0
    · exact Or.inr ⟨k, d0, a, b, _, rfl, hW.1, hW.2, hb0, hl⟩
    have hal : Al R d0 a b := hR _ _ _ (by
      by_contra hc; push Not at hc; exact hW hc)
    have hfr : op d0 a b ∉ C m (Q ∪ ((insert a (insert b U) : Finset ℕ) : Set ℕ)) := by
      intro hg
      apply hm k (by omega)
      refine hl.sol.mono le_rfl fun x hx => ?_
      simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at hx
      rcases hx with rfl | hx
      · exact hg
      · exact Or.inl (Or.inr (by simp [hx]))
    have hfU : op d0 a b ∉ U := fun h => hfr (Or.inl (Or.inr (by simp [h])))
    have hfa : op d0 a b ≠ a := fun h => hfr (Or.inl (Or.inr (by simp [h])))
    have hfb : op d0 a b ≠ b := fun h => hfr (Or.inl (Or.inr (by simp [h])))
    have hfR : R (op d0 a b) = 0 := by
      by_contra h; exact hfr (Or.inl (Or.inl h))
    have hm' : ∀ q < k, ¬ Sol Z0 m T q (C m (Q ∪ ((insert (op d0 a b) U : Finset ℕ) : Set ℕ))) := by
      intro q hq hs
      refine hm (q + 1) (by omega) (.bi (d := d0) (a := a) (b := b) (Or.inl (Or.inr (by simp))) (Or.inl (Or.inr (by simp))) (al0 _ _ _) (hs.mono le_rfl ?_))
      rintro x ((hx | hx) | hx)
      · exact Or.inr (Or.inl (Or.inl hx))
      · simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at hx
        rcases hx with rfl | hx
        · exact Or.inl rfl
        · exact Or.inr (Or.inl (Or.inr (by simp [hx])))
      · exact Or.inr (Or.inr hx)
    rcases ih hm' with h | ⟨k0, d, x, y, S1, rfl, hx, hy, ⟨hxy, V, e1, rfl, hal'⟩, hl1⟩
    · exact Or.inl (.bi hab hal h)
    · set o := op d0 a b with ho
      have nx : x ≠ o := fun e => hx (e ▸ hfR)
      have ny : y ≠ o := fun e => hy (e ▸ hfR)
      have hmV : o ∈ V := by
        have : o ∈ insert x (insert y V) := by rw [← e1]; simp
        simp at this
        rcases this with h | h | h
        · exact absurd h.symm nx
        · exact absurd h.symm ny
        · exact h
      have eU : U = insert x (insert y (V.erase o)) := by
        ext z
        by_cases hz : z = o
        · subst hz
          simp [hfU, Ne.symm nx, Ne.symm ny]
        · have : z ∈ insert o U ↔ z ∈ insert x (insert y V) := by rw [e1]
          simp only [Finset.mem_insert, hz, false_or, Finset.mem_erase, ne_eq, not_false_eq_true, true_and] at this ⊢
          exact this
      refine Or.inr ⟨k0 + 1, d, x, y, insert a (insert b (insert (op d x y) (V.erase o))), rfl, hx, hy,
        ⟨hxy, insert a (insert b (V.erase o)), ?_, ?_, hal'⟩, ?_⟩
      · rw [eU]; ext z; simp only [Finset.mem_insert]
        constructor <;> (rintro (h | h | h | h | h) <;> simp only [h, true_or, or_true])
      · ext z; simp only [Finset.mem_insert]
        constructor <;> (rintro (h | h | h | h) <;> simp only [h, true_or, or_true])
      · refine .bi hab hal0 ?_
        have : insert (op d0 a b) (insert (op d x y) (V.erase o)) = insert (op d x y) V := by
          rw [Finset.insert_comm, ← ho, Finset.insert_erase hmV]
        rw [this]; exact hl1
lemma Min.Z {m T k t : ℕ} {S : Finset ℕ} (h : Min R m T k t S) : Min Z0 m T k t S := ⟨h.1.rel fun d a b _ => al0 d a b, h.2⟩
lemma NK.toR {m T k t : ℕ} {S : Finset ℕ} (h : NK Z0 m T k t S) : NK R m T k t S :=
  ⟨fun d a b S1 k0 e hb hl => h.1 d a b S1 k0 e (hb.rel fun d a b _ => al0 d a b) (hl.rel fun d a b _ => al0 d a b),
    fun a S1 k0 t0 e e' hu hl => h.2 a S1 k0 t0 e e' hu (hl.rel fun d a b _ => al0 d a b)⟩
section sound
variable {P : List ℕ} {l m g T : ℕ} (X : Ctx P l m g T)
include X
lemma one_sound (hR : RR R) (hR2 : ∀ d a b, (R a = 0 ∨ R b = 0) → Al R d a b) {K : ℕ} {f : ℕ → ℕ → ℕ → List W → Bool}
    (hF : ∀ (k t z : ℕ) (v : List W) (S : Finset ℕ), f k t z v = false → StOk P T l k z v S → (∀ w ∈ v, w.r = R w.s) →
      ∀ k' ≤ k, Live Z0 m T k' t S → (∀ q < k', ¬ Sol Z0 m T q (C m ({x | R x ≠ 0} ∪ (S : Set ℕ)))) → False)
    {k t z y : ℕ} {v : List W} {S : Finset ℕ} (hs : StOk P T l k z v S) (hcod : ∀ w ∈ v, w.r = R w.s) (hlen : 2 ≤ v.length)
    {k' : ℕ} (hk : k' ≤ k) (hl : Live Z0 m T k' t S) (hmW : ∀ q < k', ¬ Sol Z0 m T q (C m ({x | R x ≠ 0} ∪ (S : Set ℕ))))
    (hy : y = 0 ∨ (y = 1 ∧ v.length + t = k ∧ NK Z0 m T k' t S))
    (h2 : mv (look l m g K) l m g k t z v y = false)
    (h1 : ∀ a ∈ v, ∀ c ∈ v, a.s ≠ c.s → a.r ≠ 0 → c.r ≠ 0 → ∃ go : (L_meta_11040.X → L_meta_11040.X → Bool) → List L_meta_11040.X → Bool,
      node (f (k - 1) t) (pos' t) l m g (k - t - y) v.length z v go = false ∧
      ∀ h, go h (v.map (mkx (pos' t) l (wst (pos' t) l v))) = false →
        h (mkx (pos' t) l (wst (pos' t) l v) a) (mkx (pos' t) l (wst (pos' t) l v) c) = false ∨
        h (mkx (pos' t) l (wst (pos' t) l v) c) (mkx (pos' t) l (wst (pos' t) l v) a) = false) : False := by
  have hmin : Min Z0 m T k' t S := ⟨hl, fun q hq hs => hmW q hq (hs.mono le_rfl (C_mono Set.subset_union_right))⟩
  have hcard := hs.rep.card
  rcases front hR2 hl hmW with hlR | ⟨k0, d, a, b, S1, rfl, ha, hb', hb, hl1⟩
  · exact mv_sound X hR (look_sound X hR K) hs (fun w hw => Or.inr (hcod w hw)) hlen h2 k' hk ⟨hlR, hmin.2⟩ (hy.imp id fun ⟨q1, q2, q3⟩ => ⟨q1, q2, q3.toR⟩)
  · obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    obtain ⟨wa, hwa, rfl⟩ := hs.rep.mem.1 hb.sub.1
    obtain ⟨wb, hwb, rfl⟩ := hs.rep.mem.1 hb.sub.2.1
    obtain ⟨go, hg1, hg2⟩ := h1 wa hwa wb hwb hb.1 (by rw [hcod wa hwa]; exact ha) (by rw [hcod wb hwb]; exact hb')
    obtain ⟨z', r, hf, hst, hmem⟩ := node_bi X hs hmin (by omega) rfl rfl (NK.sizeB hcard hmin hk hb hl1 hy) hb hl1 (fun h xs hp a c ha hc hax hcy hxs => by
      subst hxs
      rw [hs.rep.inj ha hwa hax, hs.rep.inj hc hwb hcy]
      exact hg2 h hp) hg1
    have hfr : R (op d wa.s wb.s) = 0 := by
      by_contra hne
      refine hmW k0 (by omega) (hl1.sol.mono le_rfl fun x hx => ?_)
      have hx' := hb.sub.2.2 hx
      simp only [Finset.mem_insert] at hx'
      rcases hx' with rfl | hx'
      · exact Or.inl (Or.inl hne)
      · exact Or.inl (Or.inr hx')
    refine hF _ _ _ _ _ hf hst ?_ k0 (by simpa using hk) hl1 ?_
    · intro w hw
      rcases hmem w hw with ⟨e1, e2⟩ | h
      · rw [e1, e2, hfr]
      · exact hcod w h
    · intro q hq hs'
      refine hmW (q + 1) (by omega) (.bi (d := d) (a := wa.s) (b := wb.s) (Or.inl (Or.inr hb.sub.1)) (Or.inl (Or.inr hb.sub.2.1)) (al0 _ _ _) (hs'.mono le_rfl ?_))
      rintro x ((hx | hx) | hx)
      · exact Or.inr (Or.inl (Or.inl hx))
      · have hx' := hb.sub.2.2 hx
        simp only [Finset.mem_insert] at hx'
        rcases hx' with rfl | hx'
        · exact Or.inl rfl
        · exact Or.inr (Or.inl (Or.inr hx'))
      · exact Or.inr (Or.inr hx)
lemma or_false' {a b : Bool} (h : (Bool.rec (motive := fun _ => Bool) b true a : Bool) = false) : a = false ∧ b = false := by
  clear X
  cases a <;> simp_all
theorem look1_sound (hR : RR R) (hR2 : ∀ d a b, (R a = 0 ∨ R b = 0) → Al R d a b) {K : ℕ} : ∀ (fuel k t z : ℕ) (v : List W) (S : Finset ℕ),
    look1 l m g K fuel k t z v = false → StOk P T l k z v S → (∀ w ∈ v, w.r = R w.s) →
      ∀ k' ≤ k, Live Z0 m T k' t S → (∀ q < k', ¬ Sol Z0 m T q (C m ({x | R x ≠ 0} ∪ (S : Set ℕ)))) → False := by
  intro fuel
  induction fuel with
  | zero => intro k t z v S h; simp [look1] at h
  | succ fuel ih =>
    intro k t z v S h hs hcod k' hk hl hmW
    change (Bool.rec (motive := fun _ => Bool) (tst (pos t) l (k + 1 - t) v (fun y => Bool.rec (motive := fun _ => Bool) (mv (look l m g K) l m g k t z v y) true
        (node (look1 l m g K fuel (k - 1) t) (pos t) l m g (k - t - y) v.length z v pairsS))) true (Nat.ble v.length 1) : Bool) = false at h
    rw [bR, pos_eq] at h
    cases h0 : Nat.ble v.length 1 with
    | true => rw [h0] at h; simp at h
    | false =>
      rw [h0, cond_false] at h
      have hlen : 2 ≤ v.length := by
        by_contra hc
        rw [Nat.ble_eq_true_of_le (by omega)] at h0; simp at h0
      have hmin : Min Z0 m T k' t S := ⟨hl, fun q hq hs => hmW q hq (hs.mono le_rfl (C_mono Set.subset_union_right))⟩
      obtain ⟨y, hFy, hyk⟩ := tst_sound X hs hmin hk
      have hy := (hFy _).symm.trans h
      beta_reduce at hy
      obtain ⟨hy1, hy2⟩ := or_false' X hy
      refine one_sound X hR hR2 ih hs hcod hlen hk hl hmW hyk hy2 fun a ha c hc hne har hcr => ⟨pairsS, hy1, fun h hp => ?_⟩
      exact pairs_any hp (fs_mem (List.mem_map_of_mem ha) har) (fs_mem (List.mem_map_of_mem hc) hcr) (fun e => hne (congrArg L_meta_11040.X.s e))
end sound
def rawP : List ℕ := [0x3fffffffc0000000000000000000000000007fffffff0000000001fffffffff800000000000000001fffffffe0000000000000000000000000007fffffff0000000000fffffffff800000000000000000000000000fffffffe0000000003fffffffff0000000000000000000000000000000000000000000000000000000000000000000000000003fffffff80000003ffffffe000000000fffffff000000000fffffffff000000007ffffffc000000001ffffffffe000000003ffffffffc00000001fffffffe0000000001608000001800000040000030000600587400000b04000080000c002c41803d002291450055550000040000005818030007400004000020020004008a4514015554081b0101b07a6c041e801148a2802aaa81e801148a2802aaa8000016c88000000940172005b2215c480000140000d840705c41dd0022914500555500001400000a0005499107610bb0843bd002291450055552ec421de801148a2802aaa80000025002d88805724172000005000000a94000a644176421d821ef4008a4514015554bb210fba0045228a00aaaa000005401400140013220bb1085d8421d843dd002291450055553dd002291450055550360d90e83643a43a0045228a00aaaa0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000180c004082112c40400245001020822a901000198010208245a02042088cc04082112b0100820210ac6d56b4408421250080801801810844258163abaa4b0221085205fc7ff7f608110089208040104255346ad6a04210125040200280c0842049a152c575530210808a42fe3f1ffd88088004910100024301108085526b529d560242020a8b7cfe3cff50120801150080000f0080003c040001e02208104f0080003c04410211e02208208f00908427874d34e780800008b55529e01208104636a552f00a081046dbbbcf9cf014081031594aabc02408108db776dd79e00a02009b6ded76ebc0300082db6ed6b5e1010000003e000000078000001c00000f0000e03fbfc00001f00000180001c003c03807f0000000000000000001c000003f8380f003fc0001c0000600e001c00000000000000003f000ff7fefc003f800000000000001ffbfffffffffffffc00001fc00000001fc01f0007f001fc0000003c0000f800707c01ff0000000000000000003c00001e001fdff007e00ff0003ff000000000000003fc001ff800000000000000000007f003f80007f001f000000f000003fbc001ffc01fe001f801ffc00000000000000ff000ffe0000000000000000001fc03c003c003fe00ff0007f8001f803ff000000000000003ff000000000000003feffbffbfeffeffeffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 0x7fffffffc00000000000000000000000000007fffffff0000000000fffffffffc000000000000000000000000000000000003fffffff80000000007fffffff7ffffffffc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000007fffffff00000001ffffffe0000000007ffffffc000000000fffffffff000000003fffffffbffffff80000000000000000fffffff7fffffffe000000000000000007ffffffdffffffffc000000000000000003ffffffffdfffffffc0000000000000000a8080000130200016c1100ae0482e082ea200000800000140002c0828002b900450b00005566660001400000a80180054c80082ec0843b010eef41142c0001559998bd90220bd210f5de84228580002ab3331df228580002ab3330000080000000054000c000500000651c800a80800a00030065e480450b0000556666105d80842ec04216c507b2020dd7de908450b0000556666375ef484228580002ab333000001000080000100000102103600080d800c874000ec20040eaf4021142c00015599981d07a43c8a160000aacccc0806c00d80040d0e80076100100e90f4e9e808450b000055666621e450b0000556666220de84437a110fbc8a160000aacccc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000005555ab52810422480280048002a041045300a55d5525a0410489014fff7fde82800422120a000440250000600681004249852475555b020088490a42f2cc6e7e1ffdfb280802212450001102450000229480000318c08020249a8000051901004092ca000001e4040101147404010249d01008293a000014940201012a640000219804040454d0080405266020102a661a1c75d600000840a14b7b40401022942a25bb68080204a28df1b9f7de010009490b15576b0a2aaed0000042002010228824c67ba6d9bcfbec010081254000102541918fce9b736ddfd80200819280100419236d6d77ef96ad5dfb800800c6400a00000f80000001f000001fc0000fe0003e003f8000001c000001c0003c0038003bf00000000000000000003c00003f803800f7f80003fc0003f000effc000000000000000ff80000ff000fdff80000000000000001ff8000000000000000001c00000001fc001c000f00001fdff800f80000e0003007dfc0000000000000000007f80003fc0001fc007f0000ff7ff800000000000000003fdffc000000000000000000001f000380000700001f7e007e00007f803dffc001fc00001fbfc00000000000000000ff7feffeffffffffffffff003fc01f80003dff800fe000007fbffdfbf800000000000000003ff7fffffffffffff800ff8003fe000ffe00000000000000cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc, 0x1fffffffc0000000007fffffff7ffffffffe0000000000000000000000000000000000000000000000000000000000000000000000007fffffff7ffffffc00000000000000007ffffffdffffffffe000000000000000003fffffffbffffffbffffffeffffffffe0000000000000000000000000000000007ffffffdffffffffdffffffffeffffffff80000000000000000000000000000000020000000000000004000002000000220800000004000002c004180001b4e800080000058066787800080000080000882000000d8400081d67a002000000160199e1e01e9d07a10020781f1f000002c0333c3c004000002c0333c3c0000400000002c0000c000030d07400000020000020000111000000000005806678781b08000807460f400003d3a7a10008010000005806678780780f81f000002c0333c3c0005400028000003190e4000bb2001105ead80220141f5baef480404400000160199e1e0de77c11000000b00ccf0f00d84000e8c8e80040007a1d03d080040f1f11e000005806678780080000058066787837a880883bcfbc11000000b00ccf0f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000603019020844708900090a114082089c22400066084082090e4480841117090108445c2401088482008180c10208848e12010061840411108e2404000f10044210a3901084424720222214720081440900408c0301044148e1155af65682088523046367d99a7f2fcfff680842249120211142240202092804220a13880404066008882827201108484b80442144b82b2db2ea2b2da7a8081004008421412833372db1beb7be7dc044124124022120920d99e5b50f33cb60d99e3d4dbdbdf9f408080400141120900241120a8028224281e1ecf31b7b6fdbe9b7b6fd7dcdbdb7d7d00601843100c0610c0030181882240000e00000000c000001c00000e000003eef80000001c000003c000380003bdf800000000000000000000380000f80003bbe000001f8000003f6fe0000000000000000000ffbf7fe00000fdffbfbfffffffffffffc00000000000000000001c0000001fc0001c0000f7f7fc000000e0000060000377000000000000000000003f0000003fdeffc00007f7efe00000000000000000000003fdffdffbfffffffffffffc01fc000780000077f7fc000ff0000007fbf80000001fdfeffc000000000000000000000ff7fe000000000000000007f80001fbdff8000000feff7ff000001fbfbff7fffffffffffff800000000000000003fe000003feffe00000000000000000f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0, 0x1ffffffff00000000007fffffff7ffffffffe000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000007fffffff0000000000fffffffefffffffff80000000000000000007fffffff7ffffffdffffffefffffffff00000000000000000000000000000000003fffffffbffffffbffffffeffffffffefffffff7fffffffefffffffff7fffffff0000000000000000000000000000000000000000000000000000000000000000004000000016000081400000063251c800000000054000402800002b55c80000100016000016787f802d800110badae8020028221eb75dde900200440058000059e1fe00df3e77cde77c4088080b00000b3c3fc00880b00000b3c3fc000040000000400000044102000000000016000008666ae80000000816000016787f801d0e8c1e840004000003e3c7c1e21f03e16000016787f80040040080b00000b3c3fc002c000001986a1d0000000001d3a303d080000040000f83c0f8f2f80f858000059e1fe00100200202c00002cf0ff005eaf56c8004800480a0fcde7be6f3ef880809016000016787f8009016000016787f803bcef3ef2202202202c00002cf0ff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001800064041087801416ae2cad810410e0050796783687ffdfef8a010822181402100860500011094800060318040108f02800018620080220f0500000f0800804213c4020088478804044278800028920000130600200828f040001186004010a3c1000081e0008021227801004491e00402293c028adee320804145c00499bd784de3f5fbfc02010928c00004290c03236db4c3236f530c1eda98df1befdce00084000100449410080248a08040252040e1e79c60c3cf380e1e7b18db9befde430f798c6d9befde4db9befdce6b37dfb2002100000403061000403062100201862000806184200018610004063010050000e00000003e000003c000000efef7f80000000007c000003800003bddf800000000000000000000003f800000fbfbf8000000001fbfddff800000000000000000000000ffbf7feff7fe0000000000000000000000000000000000000001c0000007c000001ddf7e00000000003e0000006efbf800000000000000000000003f7fbdff800000000007f7efeff7ffbff7fffffffffffff80000000000000000000001fc000007bbfbff000000000ff7ef7ff000000000001fdfeffdfbfdffdfffffffffffffe00000000000000000000007fbfdfc000000000000feff7ff7fbffc00000000000000000000000000000000000003feffbff80000000000000000000000ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00, 0x7fffffff8000000000000000003fffffffbfffffffff0000000000000000000000000000000000003fffffffc000000000000000001fffffffdfffffffff0000000000000000000000000000000000007fffffff7ffffffffe0000000000000000000000000000000000007fffffff7ffffffdffffffefffffffff7ffffffdffffffffefffffffff7fffffff800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000160000010180000000cc3483a000000000000000b00000081b4d1e80000000800000004c26187f80000698c83a000000000000000f07881f1e47c40f8801309861fe00001000040000000010000026130c3fc0000000026130c3fc00016c00001105d756d280004000044000903aeda9dd00008000008000004c26187f80003e6f29df3794ef9896220004000110000004c26187f8000000880000026130c3fc0001756d74a0000110000480040de7ca7be6f3129f795888000880008000001309861fe00000044000000984c30ff00006f37989f29ef29ef2c44000220000880010000004c26187f8000000004c26187f80003c0f02f03c0bc0bc000984c30ff0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000600c0004820f801004030300012081f004010078000110411f000221043e00044208f80015a5e2e708108042048120f0000b659f849bfa7feff8108030003108841c004411107800884083800ab28f1ce40804084240900f00059925f84dfd3e3ffe1040060031044043802208811e00882001c013cc94fc36fcfc79ff2100018061110103808422020f010888007013c38e38f3c38c63cf18e31edf9bcf9cf3c318e3dbf379e79edf9b9f3cf6fcb9ce79000000790000009000001e0c0204106400000f0602041060c020410f0c0408032000003c18040820c18040841e0c020041830082083c3000820c1808421e40103e0000000780000003ddfddfe000000000000001f00000003bddbf80000000000000000000000000003fbbddfe000000000000001fbfddffbf6feeffddfffffffffffffe00000000000000000000000000000000000000000000000001fc00000007dfdfdfc0000000000000003eefbdff00000000000000000000000000003f7fbdffbfdeffdfdff000000000000000000000000000000000000000000000000001fdfdf7f0000000000000000ff7ef7ff7fbfbdffdffc000000000000000000000000000000000000000000000000007fbfdfdfbdffbdffbfe000000000000000000000000000000000000000000000000003feffbffbfeffeffeffffffffffffffffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000, 0x1ffffffff7fffffffff0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003fffffffdfffffffefffffffffc000000000000000000000000000000000000000000000000000007fffffff7ffffffffefffffffefffffffffbfffffffff7ffffffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000280000000029a4428c80000000000010000000001d6d95d6e800008000100000000101800381f80000037329dbcd31372334a31378000011000000000006000e07e0000000000400004400000000c001c0fc000000000c001c0fc00000034c84341d000000000000000000000001c410c1e4472f02208081e1800381f8000000000001000000000000000000000000201800381f800000000000000c001c0fc000001b989a7353373de462709a7400000220000000400600000000000008806000e07e000000000002003000703f00000070381f10317030f03f880e07c0702f010202e01800381f8000001e01800381f800000000003000000000003000703f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000018010181903f0000219b3fc0c9e7ffdfff8860180040e2081e0010c4207c00218840f0008600603003003018019003f00043001e000e10043f0006003c001c20107e00188021f80031008fc003323cfe0f991e7f07cfe1fcfff980046007080213c0060011801c200827c00c40109e00310044e00630f18ffc6f8fe79ffc61e31ff8de3f9f3ff37c7f3cffe6f1fce7fe004003f0004007c002003e0100c081f000400fc02018107e0100c103f0080c00f8002001f8004003f002003e0100c081f801001f0080c081f8100c081f00018103c00400fc02018103f02018107e0100c087e0403040fc0406103f0203003e008678000000007bedf7bf80000000000000000000001f7dddf7f80000000000000000000000000000000003fbbddfefbfbfbbbef7fbfc000000000000000000000000000000000000000000000000000000000000000000000000000000001fddddfdff000000000000000000000003eefbdff6efbfb777dfdff7fffffffffffff8000000000000000000000000000000000000000000000000000000000000000000001fdfdf7f7bbfbff77f7fdf7e00000000000000000000000000000000000000000000000000000000000000000000007fbfdfdfbdffbdffbfefeff7ff7fbffdfbfbff7fffffffffffffbff7fffffffffffff8000000000000000000000000000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000, 0x7fffffffbfffffffdfffffffff8000000000000000000000000000000000000000000000000000003fffffffdfffffffefffffffffdfffffffdfffffffff7fffffff7ffffffffefffffffffbffffffff0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000019a2611a1d0000000000000020000000000000040e08c4e0f13899f10081138f1023e00703fe0000000000000200000000000000400000000000400000001c0ff8000000000000000000000001000381ff000000000000381ff00000001b99d5b9de69b989cd91a74a6e77988e1000001100000000000011000703fe000000000000100000088001800000000000020000703fe00000000000011000381ff00000001c1f1c7c62381e067c7f1c78e040c7c0703e31781ff101c0f010101f0001c0ff80000000e0780bc000e07fc00000000000000001800080300000000000000000030000703fe000000010000703fe000000000000000000c0000000e07fc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000600602061fc000020603c0000e040fe0000181e00007040fe00003083f800006107f0000186c7fc07c363fe03e1fe3ffff8c086000702047c0001810c000e0411f800061023e0000c208f0000c3c30fff01e187ff80ff1f8fffe1e187ff81fe3e3fff87861ffe07f8fc7fff0ff1f1fffc3fc78fff84001f000300807e0008003e00060201fc00180403f00030100f8004000fc004000f801000fc0060100fe004001f000c0201f80060101fc0030001f0020007e002000fc020007c0060100fe008007e0030100fe0060100fe0030201fc04001f000c0201fc00c0201f80060100f80180407f0018081fc00c0007c008187beeefbeff0000000000000000000000000000001f7dddf7fbbddbfbbddfbbdfbbf7f7fffffffffffff80000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001fddddfdff7dfdfdfdddf7ef7f7fdfdff8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001fdfdf7f7bbfbff77f7fdf7eff7ef7ff7fbfbdffdffdfdfeffdfbfdffdfffffffffffffeff7feffeffffffffffffff0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000, 0x7fffffffdfffffffffc00000000000000000000000000000000000000000000000000000007fffffffbfffffffdfffffffffbfffffffbfffffffff7fffffff7ffffffffdfffffffffbffffffff800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000053cacdbcde52099531299b9dbc8c4a6134cd373780000000000001000000000002020607fc000000000000000000000000000400000000000000000880181ff0000000000000000000000010000303fe000000000110303fe0000000001c1119c1e071c1f1f119c78c70781f1fe208e31e00881024471f1e0607fc000000000207031e03818f01f1fc404080e05e03c0607fc000000000381f01e0303fe000000000000000000000000000000000000004000000018018000000000000100181ff000000000000000c00c0ff800000000000000000000001000000000000000000000000607fc000000000200607fc00000000000000000000000c00c0ff8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000007ff803f81ffffffc381c0000f007f000000e0600007807f000001c0fc00000381f800000e0707fff80383fffc01fc3fffff0307fff803f87ffffe060ffff007e1fffff81fc3fffff03f0fffff0003f0000001f80000801ff0000001f80001003fc0000007e0000400ff80000801fe00002007f000000fe0000400ff8000001fc0000803fe00002007fc0000401ff0000007f0000007f000003f0000801ff0000007e0001003fe0000801fe0000400fe000003f8000007f000003f8000801ff000001f8000401ff0000801ff0000403fe000007e0001003fe0001003fe0000801ff0002007f8000000fe0001003f80000e07beeefbeff7bedf7bfbddfddfeefef7fbeefbfbfc00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001fddddfdff7dfdfdfdddf7ef7f7fdfdffbeefbdff6efbfb777dfdff7fffffffffffffbf7fbdffbfdeffdfdff7f7efeff7ffbff7fffffffffffffbfdffdffbfffffffffffffc0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000, 0x7fffffffdfffffffffdffffffff7fffffffff7fffffff7ffffffffefffffffffdfffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000620c8e20e063cde63e311c11c0cf8c7e388e38381071190702010202391e201023c407f800000000000382311c0e3e383238c7e38103811e0200808f011fe000000000000e020780e078081e0203fc000000000001e03fc0000000000000000000000000000000000000000010000000000000200000100007f8000000000000000000000000000000000000006000007f800000000000001000003fc000000000000000000000002000000000000000000000000000000000000000200001fe00000000000000000000ff000000000000000000000000000000000004000030000000007f8000000000000007f80000000000000000000000000000ff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000007ffffc001fffffffc01fffff0007fffffff007ffff8007ffffffe00fffffffc01fffffff007f8000003fc000001ffc0000003f8000003ff80000007f0000007fe0000001ffc0000003ff0000003fc000001fe000000ffe0000001fe000001ffc0000007f8000007ff0000000ffe0000003ff8000007f0000007ff0000000fe000000ffc0000003ff80000007fe0000007f8000007f800001fc00000ffe0000007f800001ffc000000ffe0000007ff000003fc000003f800003fc00000ffe000000fe000007fe000000ffe0000007fc000007f800001ffc000001ffc000000ffe000003ff8000001ff000001ffc00000f007beeefbeff7bedf7bfbddfddfeefef7fbeefbfbfdf7dddf7fbbddbfbbddfbbdfbbf7f7fffffffffffffbfbbddfefbfbfbbbef7fbfdfbfddffbf6feeffddfffffffffffffeffbf7feff7fefdffbfbfffffffffffffdffbfffffffffffffc0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000]
def xw (e : ℕ × ℕ) : ℕ := rawP.getD e.1 0 ||| rawP.getD e.2 0
def rawL (E : List (ℕ × ℕ)) : List ℕ := rawP ++ E.map xw
def six : List (ℕ × ℕ) := []
def rawG : List ℕ := rawL six
def FPM : ℕ := 2 ^ 512 - 1
def FULL : ℕ := 2 ^ NN - 1
def TG : ℕ := 0x7fffffffdfffffffffdffffffff7fffffffff7fffffff7ffffffffefffffffffdfffffffff7fffffffbfffffffdfffffffffbfffffffbfffffffff7fffffff7ffffffffdfffffffffbffffffffbfffffffdfffffffefffffffffdfffffffdfffffffff7fffffff7ffffffffefffffffffbffffffff7fffffff7ffffffffefffffffefffffffffbfffffffff7ffffffff7fffffff7ffffffdffffffefffffffff7ffffffdffffffffefffffffff7fffffffbfffffffbffffffbffffffeffffffffefffffff7fffffffefffffffff7fffffff7ffffffdffffffffdffffffffeffffffffbffffffffdfffffffdfffffffefff7beeefbeff7bedf7bfbddfddfeefef7fbeefbfbfdf7dddf7fbbddbfbbddfbbdfbbf7f7fffffffffffffbfbbddfefbfbfbbbef7fbfdfbfddffbf6feeffddfffffffffffffeffbf7feff7fefdffbfbfffffffffffffdffbfffffffffffffdfddddfdff7dfdfdfdddf7ef7f7fdfdffbeefbdff6efbfb777dfdff7fffffffffffffbf7fbdffbfdeffdfdff7f7efeff7ffbff7fffffffffffffbfdffdffbfffffffffffffdfdfdf7f7bbfbff77f7fdf7eff7ef7ff7fbfbdffdffdfdfeffdfbfdffdfffffffffffffeff7feffeffffffffffffff7fbfdfdfbdffbdffbfefeff7ff7fbffdfbfbff7fffffffffffffbff7fffffffffffffbfeffbffbfeffeffefffffffffffffffffffffffffffffffffffffffffffffafffffffffffffffffffffefefffffafafffffffffffefffcfffffffffffafff0fffefffcffeeffccfefefcfcaaaa0000
def selectors : List ℕ := rawP ++ [0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc00000003fffffffffffffffffffffffffff80000000fffffffffe0000000007ffffffffffffffffe00000001fffffffffffffffffffffffffff80000000ffffffffff0000000007ffffffffffffffffffffffffff00000001fffffffffc000000000fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc00000007ffffffc0000001fffffffff0000000fffffffff000000000ffffffff80000003ffffffffe000000001ffffffffc000000003fffffffe00000001fffffffffe9f7fffffe7ffffffbfffffcffff9ffa78bfffff4fbffff7ffff3ffd3be7fc2ffdd6ebaffaaaafffffbffffffa7e7fcfff8bffffbffffdffdfffbff75baebfeaaabf7e4fefe4f8593fbe17feeb75d7fd5557e17feeb75d7fd5557ffffe9377ffffff6bfe8dffa4ddea3b7ffffebffff27bf8fa3be22ffdd6ebaffaaaaffffebfffff5fffab66ef89ef44f7bc42ffdd6ebaffaaaad13bde217feeb75d7fd5557fffffdaffd2777fa8dbe8dfffffaffffff56bfff59bbe89bde27de10bff75baebfeaaab44def045ffbadd75ff5555fffffabfebffebffecddf44ef7a27bde27bc22ffdd6ebaffaaaac22ffdd6ebaffaaaafc9f26f17c9bc5bc5ffbadd75ff555500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffe7f3ffbf7deed3bfbffdbaffefdf7dd56fefffe67fefdf7dba5fdfbdf7733fbf7deed4feff7dfdef5392a94bbf7bdedaff7f7fe7fe7ef7bbda7e9c5455b4fddef7adfa03800809f7eeff76df7fbfefbdaacb95295fbdefedafbfdffd7f3f7bdfb65ead3a8aacfdef7f75bd01c0e00277f77ffb6efefffdbcfeef7f7aad94ad62a9fdbdfdf5748301c300afedf7feeaff7ffff0ff7fffc3fbfffe1fddf7efb0ff7fffc3fbbefdee1fddf7df70ff6f7bd878b2cb187f7ffff74aaad61fedf7efb9c95aad0ff5f7efb9244430630febf7efcea6b5543fdbf7ef72488922861ff5fdff64921289143fcfff7d2491294a1efeffffffc1fffffff87fffffe3fffff0ffff1fc0403ffffe0fffffe7fffe3ffc3fc7f80ffffffffffffffffffe3fffffc07c7f0ffc03fffe3ffff9ff1ffe3ffffffffffffffffc0fff0080103ffc07fffffffffffffe00400000000000003ffffe03fffffffe03fe0fff80ffe03ffffffc3ffff07ff8f83fe00ffffffffffffffffffc3ffffe1ffe0200ff81ff00fffc00ffffffffffffffc03ffe007fffffffffffffffffff80ffc07fff80ffe0ffffff0fffffc043ffe003fe01ffe07fe003ffffffffffffff00fff001ffffffffffffffffffe03fc3ffc3ffc01ff00fff807ffe07fc00ffffffffffffffc00ffffffffffffffc01004004010010010000000000000055555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555555, 0x800000003ffffffffffffffffffffffffffff80000000ffffffffff0000000003fffffffffffffffffffffffffffffffffffc00000007fffffffff800000008000000003ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff80000000fffffffe0000001fffffffff80000003fffffffff000000000ffffffffc000000040000007ffffffffffffffff0000000800000001fffffffffffffffff80000002000000003fffffffffffffffffc00000000200000003ffffffffffffffff57f7ffffecfdfffe93eeff51fb7d1f7d15dfffff7fffffebfffd3f7d7ffd46ffbaf4ffffaa9999fffebfffff57fe7ffab37ff7d13f7bc4fef110beebd3fffeaa6667426fddf42def0a217bdd7a7fffd54ccce20dd7a7fffd54cccfffff7ffffffffabfff3fffafffff9ae37ff57f7ff5fffcff9a1b7fbaf4ffffaa9999efa27f7bd13fbde93af84dfdf228216f7baf4ffffaa9999c8a10b7bdd7a7fffd54cccfffffeffff7ffffefffffefdefc9fff7f27ff378bfff13dffbf150bfdeebd3fffeaa6667e2f85bc375e9ffff553333f7f93ff27ffbf2f17ff89effeff16f0b1617f7baf4ffffaa9999de1baf4ffffaa9999ddf217bbc85eef04375e9ffff55333300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000aaaa54ad7efbddb7fd7ffb7ffd5fbefbacff5aa2aada5fbefb76feb00080217d7ffbddedf5fffbbfdaffff9ff97effbdb67adb8aaaa4fdff77b6f5bd0d339181e00204d7f7fddedbafffeefdbaffffdd6b7ffffce73f7fdfdb657ffffae6feffbf6d35fffffe1bfbfefeeb8bfbfefdb62feff7d6c5ffffeb6bfdfefed59bffffde67fbfbfbab2ff7fbfad99fdfefd599e5e38a29fffff7bf5eb484bfbfefdd6bd5da4497f7fdfb5d720e460821fefff6b6f4eaa894f5d5512fffffbdffdfefdd77db39845926430413feff7edabfffefdabe6e7031648c922027fdff7e6d7feffbe6dc929288106952a2047ff7ff39bff5fffff07ffffffe0fffffe03ffff01fffc1ffc07fffffe3fffffe3fffc3ffc7ffc40fffffffffffffffffffc3ffffc07fc7ff0807fffc03fffc0fff1003fffffffffffffff007ffff00fff02007fffffffffffffffe007fffffffffffffffffe3fffffffe03ffe3fff0ffffe02007ff07ffff1fffcff8203ffffffffffffffffff807fffc03fffe03ff80ffff008007ffffffffffffffffc02003ffffffffffffffffffffe0fffc7ffff8ffffe081ff81ffff807fc2003ffe03ffffe0403fffffffffffffffff0080100100000000000000ffc03fe07fffc2007ff01fffff8040020407ffffffffffffffffc00800000000000007ff007ffc01fff001ffffffffffffff33333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333333, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe00000003fffffffff800000008000000001ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8000000080000003ffffffffffffffff80000002000000001fffffffffffffffffc0000000400000040000001000000001fffffffffffffffffffffffffffffffff80000002000000002000000001000000007ffffffffffffffffffffffffffffffffdfffffffffffffffbfffffdffffffddf7fffffffbfffffd3ffbe7fffe4b17fff7fffffa7f998787fff7fffff7ffff77dffffff27bfff7e2985ffdffffffe9fe661e1fe162f85effdf87e0e0fffffd3fccc3c3ffbfffffd3fccc3c3ffffbfffffffd3ffff3ffffcf2f8bffffffdfffffdffffeeefffffffffffa7f998787e4f7fff7f8b9f0bffffc2c585efff7feffffffa7f998787f87f07e0fffffd3fccc3c3fffabfffd7fffffce6f1bfff44dffeefa1527fddfebe0a4510b7fbfbbfffffe9fe661e1f21883eeffffff4ff330f0ff27bfff173717ffbfff85e2fc2f7ffbf0e0ee1fffffa7f998787ff7fffffa7f998787c8577f77c43043eeffffff4ff330f0f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ff9fcfe6fdf7bb8f76fff6f5eebf7df763ddbfff99f7bf7df6f1bb7f7beee8f6fef7bba3dbfef77b7dff7e7f3efdf77b71edfeff9e7bfbeeef71dbfbfff0effbbdef5c6fef7bbdb8dfddddeb8dff7ebbf6ffbf73fcfefbbeb71eeaa509a97df77adcfb9c98266580d0300097f7bddb6edfdeeebddbfdfdf6d7fbddf5ec77fbfbf99ff777d7d8dfeef7b7b47fbbdebb47d4d24d15d4d25857f7effbff7bdebed7ccc8d24e414841823fbbedbedbfddedf6df2661a4af0cc349f2661c2b24242060bf7f7fbffebeedf6ffdbeedf57fd7ddbd7e1e130ce48490241648490282324248282ff9fe7bceff3f9ef3ffcfe7e77ddbffff1ffffffff3fffffe3fffff1fffffc1107ffffffe3fffffc3fffc7fffc4207ffffffffffffffffffffc7ffff07fffc441fffffe07fffffc0901fffffffffffffffffff0040801fffff020040400000000000003fffffffffffffffffffe3ffffffe03fffe3ffff080803ffffff1fffff9ffffc88ffffffffffffffffffffc0ffffffc021003ffff808101ffffffffffffffffffffffc0200200400000000000003fe03fff87fffff880803fff00ffffff80407ffffffe0201003fffffffffffffffffffff00801fffffffffffffffff807fffe042007ffffff0100800fffffe040400800000000000007ffffffffffffffffc01fffffc01001fffffffffffffffff0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f, 0xffffffffffffffffffe00000000ffffffffff800000008000000001fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff80000000ffffffffff000000010000000007ffffffffffffffffff80000000800000020000001000000000ffffffffffffffffffffffffffffffffffc0000000400000040000001000000001000000080000000100000000080000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffbfffffffe9ffff7ebffffff9cdae37fffffffffabfffbfd7ffffd4aa37ffffefffe9ffffe987807fd27ffeef452517fdffd7dde148a2216ffdffbbffa7ffffa61e01ff20c188321883bf77f7f4fffff4c3c03ff77f4fffff4c3c03ffffbfffffffbffffffbbefdffffffffffe9fffff7999517fffffff7e9ffffe987807fe2f173e17bfffbfffffc1c383e1de0fc1e9ffffe987807ffbffbff7f4fffff4c3c03ffd3fffffe6795e2fffffffffe2c5cfc2f7fffffbffff07c3f070d07f07a7ffffa61e01ffeffdffdfd3ffffd30f00ffa150a937ffb7ffb7f5f032184190c1077f7f6fe9ffffe987807ff6fe9ffffe987807fc4310c10ddfddfddfd3ffffd30f00ff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000fe7fff9bfbef787febe951d3527efbef1ffaf86987c97800201075fef7dde7ebfdeff79fafffeef6b7fff9fce7fbfef70fd7fffe79dff7fddf0fafffff0f7ff7fbdec3bfdff77b877fbfbbd877fffd76dffffecf9ffdff7d70fbfffee79ffbfef5c3effff7e1fff7fdedd87feffbb6e1ffbfdd6c3fd75211cdf7fbeba3ffb664287b21c0a0403fdfef6d73ffffbd6f3fcdc924b3cdc90acf3e1256720e410231fff7bfffeffbb6beff7fdb75f7fbfdadfbf1e18639f3c30c7f1e184e724641021bcf0867392641021b24641023194c8204dffdefffffbfcf9efffbfcf9deffdfe79dfff7f9e7bdfffe79efffbf9cfeffaffff1fffffffc1fffffc3ffffff1010807fffffffff83fffffc7ffffc42207ffffffffffffffffffffffc07fffff040407ffffffffe04022007fffffffffffffffffffffff004080100801fffffffffffffffffffffffffffffffffffffffe3ffffff83fffffe22081ffffffffffc1ffffff910407ffffffffffffffffffffffc08042007ffffffffff80810100800400800000000000007fffffffffffffffffffffe03fffff8440400fffffffff00810800fffffffffffe0201002040200200000000000001ffffffffffffffffffffff8040203ffffffffffff0100800804003fffffffffffffffffffffffffffffffffffffc01004007ffffffffffffffffffffff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff800000007fffffffffffffffffc00000004000000000ffffffffffffffffffffffffffffffffffffc00000003fffffffffffffffffe00000002000000000ffffffffffffffffffffffffffffffffffff800000008000000001ffffffffffffffffffffffffffffffffffff8000000080000002000000100000000080000002000000001000000000800000007ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe9fffffefe7fffffff33cb7c5fffffffffffffff4ffffff7e4b2e17fffffff7fffffffb3d9e7807ffff96737c5fffffffffffffff0f877e0e1b83bf077fecf679e01ffffeffffbffffffffefffffd9ecf3c03ffffffffd9ecf3c03fffe93ffffeefa28a92d7fffbffffbbfff6fc5125622ffff7fffff7fffffb3d9e7807fffc190d620c86b106769ddfffbfffeeffffffb3d9e7807ffffff77fffffd9ecf3c03fffe8a928b5ffffeeffffb7ffbf2183584190ced6086a777fff77fff7fffffecf679e01ffffffbbffffff67b3cf00ffff90c86760d610d610d3bbfffddffff77ffeffffffb3d9e7807ffffffffb3d9e7807fffc3f0fd0fc3f43f43fff67b3cf00ffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000f9ff3fffb7df07feffbfcfcfffedf7e0ffbfeff87fffeefbee0fffddefbc1fffbbdf707ffea5a1d18f7ef7fbdfb7edf0ffff49a607b6405801007ef7fcfffcef77be3ffbbeeef87ff77bf7c7ff54d70e31bf7fbf7bdbf6ff0fffa66da07b202c1c001efbff9ffcefbbfbc7fddf77ee1ff77dffe3fec336b03c903038600defffe7f9eeefefc7f7bddfdf0fef777ff8fec3c71c70c3c739c30e71ce1206430630c3ce71c240c861861206460c30903463186ffffff86ffffff6fffffe1f3fdfbef9bfffff0f9fdfbef9f3fdfbef0f3fbf7fcdfffffc3e7fbf7df3e7fbf7be1f3fdffbe7cff7df7c3cfff7df3e7f7bde1bfefc1fffffff87ffffffc2202201ffffffffffffffe0fffffffc422407fffffffffffffffffffffffffffc0442201ffffffffffffffe0402200409011002200000000000001fffffffffffffffffffffffffffffffffffffffffffffffffe03fffffff82020203fffffffffffffffc1104200ffffffffffffffffffffffffffffc080420040210020200ffffffffffffffffffffffffffffffffffffffffffffffffffe0202080ffffffffffffffff00810800804042002003ffffffffffffffffffffffffffffffffffffffffffffffffff8040202042004200401ffffffffffffffffffffffffffffffffffffffffffffffffffc0100400401001001000000000000000000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff, 0xffffffffffffffffffe000000008000000000fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc00000002000000010000000003fffffffffffffffffffffffffffffffffffffffffffffffffffff800000008000000001000000010000000004000000000800000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffd7ffffffffd65bbd737fffffffffffefffffffffe2926a2917ffff7fffeffffffffefe7ffc7e07fffffc8cd62432cec8dccb5cec87ffffeefffffffffff9fff1f81ffffffffffbffffbbffffffff3ffe3f03fffffffff3ffe3f03ffffffcb37bcbe2fffffffffffffffffffffffe3bef3e1bb8d0fddf7f7e1e7ffc7e07fffffffffffeffffffffffffffffffffffffdfe7ffc7e07ffffffffffffff3ffe3f03fffffe467658cacc8c21b9d8f658bfffffddfffffffbff9fffffffffffff77f9fff1f81fffffffffffdffcfff8fc0ffffff8fc7e0efce8fcf0fc077f1f83f8fd0fefdfd1fe7ffc7e07fffffe1fe7ffc7e07ffffffffffcfffffffffffcfff8fc0ffffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000e7fefe7e6fc0ffffde64c03f3618002000779fe7ffbf1df7e1ffef3bdf83ffde77bf0fff79ff9fcffcffcfe7fe6ffc0fffbcffe1fff1effbc0fff9ffc3ffe3dfef81ffe77fde07ffceff703ffccdc301f066e180f8301e0300067ffb9ff8f7fdec3ff9ffee7fe3dff7d83ff3bfef61ffceffbb1ff9cf0e700390701860039e1ce00721c060c00c8380c300190e031801ffbffc0fffbff83ffdffc1feff3f7e0fffbff03fdfe7ef81feff3efc0ff7f3ff07ffdffe07ffbffc0ffdffc1feff3f7e07feffe0ff7f3f7e07eff3f7e0fffe7efc3ffbff03fdfe7efc0fdfe7ef81feff3f781fbfcfbf03fbf9efc0fdfcffc1ff7987ffffffff841208407fffffffffffffffffffffe082220807fffffffffffffffffffffffffffffffffc0442201040404441080403ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe022220200fffffffffffffffffffffffc110420091040488820200800000000000007ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe02020808440400880802081ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8040202042004200401010080080400204040080000000000000400800000000000007ffffffffffffffffffffffffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff800000004000000020000000007fffffffffffffffffffffffffffffffffffffffffffffffffffffc0000000200000001000000000200000002000000000800000008000000001000000000400000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe65d9ee5e2ffffffffffffffdffffffffffffffbf1f73b1f0ec7660eff7eec70efdc1ff8fc01fffffffffffffdffffffffffffffbfffffffffffbfffffffe3f007fffffffffffffffffffffffefffc7e00ffffffffffffc7e00fffffffe4662a4621964676326e58b591886771efffffeeffffffffffffeefff8fc01ffffffffffffeffffff77ffe7ffffffffffffdffff8fc01ffffffffffffeefffc7e00fffffffe3e0e3839dc7e1f98380e3871fbf383f8fc1ce87e00efe3f0fefefe0fffe3f007fffffff1f87f43fff1f803ffffffffffffffffe7fff7fcffffffffffffffffffcffff8fc01fffffffeffff8fc01ffffffffffffffffff3fffffff1f803fffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000009ff9fdf9e03ffffdf9fc3ffff1fbf01ffffe7e1ffff8fbf01ffffcf7c07ffff9ef80ffffe793803f83c9c01fc1e01c000073f79fff8fdfb83fffe7ef3fff1fbee07fff9efdc1ffff3df70ffff3c3cf000fe1e78007f00e070001e1e78007e01c1c0007879e001f807038000f00e0e0003c03870007bffe0fffcff7f81fff7ffc1fff9fdfe03ffe7fbfc0fffcfeff07ffbfff03ffbfff07fefff03ff9feff01ffbffe0fff3fdfe07ff9fefe03ffcfffe0ffdfff81ffdfff03fdfff83ff9feff01ff7ff81ffcfeff01ff9feff01ffcfdfe03fbffe0fff3fdfe03ff3fdfe07ff9feff07fe7fbf80ffe7f7e03ff3fff83ff7e78411104100ffffffffffffffffffffffffffffffe0822208044224044220442044080800000000000007ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe022220200820202022208108080202007ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe020208084404008808020810081080080404200200202010020402002000000000000010080100100000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff, 0x8000000020000000003fffffffffffffffffffffffffffffffffffffffffffffffffffffff800000004000000020000000004000000040000000008000000080000000020000000004000000007fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffac35324321adf66aced664624373b59ecb32c8c87ffffffffffffefffffffffffdfdf9f803fffffffffffffffffffffffffffbfffffffffffffffff77fe7e00fffffffffffffffffffffffeffffcfc01fffffffffeefcfc01fffffffffe3eee63e1f8e3e0e0ee638738f87e0e01df71ce1ff77efdbb8e0e1f9f803fffffffffdf8fce1fc7e70fe0e03bfbf7f1fa1fc3f9f803fffffffffc7e0fe1fcfc01ffffffffffffffffffffffffffffffffffffffbfffffffe7fe7ffffffffffffeffe7e00fffffffffffffff3ff3f007ffffffffffffffffffffffeffffffffffffffffffffffff9f803fffffffffdff9f803fffffffffffffffffffffff3ff3f007fffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008007fc07e0000003c7e3ffff0ff80ffffff1f9ffff87f80fffffe3f03fffffc7e07fffff1f8f80007fc7c0003fe03c00000fcf80007fc07800001f9f0000ff81e000007e03c00000fc0f00000fffc0ffffffe07ffff7fe00ffffffe07fffeffc03ffffff81ffffbff007ffff7fe01ffffdff80ffffff01ffffbff007fffffe03ffff7fc01ffffdff803ffffbfe00ffffff80ffffff80fffffc0ffff7fe00ffffff81fffeffc01ffff7fe01ffffbff01fffffc07fffff80fffffc07fff7fe00fffffe07fffbfe00ffff7fe00ffffbfc01fffff81fffeffc01fffeffc01ffff7fe00fffdff807ffffff01fffeffc07ffff1f84111041008412084042202201101080411040403fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe022220200820202022208108080202004110420091040488820200800000000000004080420040210020200808101008004008000000000000040200200400000000000003fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff, 0x80000000200000000020000000080000000008000000080000000010000000002000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff9df371df1f9c3219c1cee3ee3f307381c771c7c7ef8ee6f8fdfefdfdc6e1dfefdc3bf807fffffffffffc7dcee3f1c1c7cdc7381c7efc7ee1fdff7f70fee01ffffffffffff1fdf87f1f87f7e1fdfc03fffffffffffe1fc03fffffffffffffffffffffffffffffffffffffffffefffffffffffffdfffffeffff807ffffffffffffffffffffffffffffffffffffff9fffff807fffffffffffffefffffc03fffffffffffffffffffffffdfffffffffffffffffffffffffffffffffffffffdffffe01ffffffffffffffffffff00fffffffffffffffffffffffffffffffffffbffffcfffffffff807ffffffffffffff807ffffffffffffffffffffffffffff00ffffffffffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000800003ffe00000003fe00000fff80000000ff800007ff80000001ff00000003fe0000000ff807fffffc03fffffe003ffffffc07fffffc007ffffff80ffffff801ffffffe003ffffffc00ffffffc03fffffe01ffffff001ffffffe01fffffe003ffffff807fffff800fffffff001ffffffc007fffff80ffffff800fffffff01ffffff003ffffffc007ffffff801ffffff807fffff807ffffe03fffff001ffffff807ffffe003ffffff001ffffff800fffffc03fffffc07ffffc03fffff001ffffff01fffff801ffffff001ffffff803fffff807ffffe003fffffe003ffffff001fffffc007fffffe00fffffe003fffff0ff8411104100841208404220220110108041104040208222080442240442204420440808000000000000040442201040404441080402040220040901100220000000000000100408010080102004040000000000000200400000000000003fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff]
def kz (Z : ℕ) : ℕ := (List.range 18).foldr (fun i x => bif Nat.testBit Z i then Nat.lor x (Nat.land (Nat.lor (selectors.getD i 0) (Nat.shiftRight (selectors.getD i 0) NN)) FULL) else x) 0
def lz (Z : ℕ) : ℕ := Nat.land AA (Nat.xor (kz Z) FULL)
def fz (Z : ℕ) : ℕ := Nat.land FPM (Nat.xor (kz Z) FULL)
def mz (Z : ℕ) : ℕ := Nat.lor (Nat.lor (lz Z) (fz Z)) (Nat.shiftLeft (lz Z) NN)
def tz (Z : ℕ) : ℕ := Nat.land TG (mz Z)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma AA_TG : AA &&& TG = AA := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma TG_lt : TG < 2 ^ NN := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma AA_lt : AA < 2 ^ NN := by decide +kernel
lemma lz_lg (Z i : ℕ) (h : (lz Z).testBit i = true) : Lg NN (mz Z) (tz Z) i ∧ AA.testBit i = true := by
  have hA : AA.testBit i = true := by
    simp only [lz, nl, Nat.testBit_and, Bool.and_eq_true] at h; exact h.1
  have hT : TG.testBit i = true := by
    have := congrArg (fun x => x.testBit i) AA_TG
    simp [hA] at this; exact this
  have m1 : (mz Z).testBit i = true := by simp [mz, no, h]
  have m2 : (mz Z).testBit (NN + i) = true := by
    simp only [mz, no, Nat.testBit_or, Nat.shiftLeft_eq, Bool.or_eq_true]
    right
    change (lz Z <<< NN).testBit (NN + i) = true
    rw [Nat.testBit_shiftLeft]; simp [h]
  refine ⟨⟨m1, m2, ?_, ?_⟩, hA⟩
  · simp only [tz, nl, Nat.testBit_and, hT, m1]; rfl
  · simp only [tz, nl, Nat.testBit_and]
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le TG_lt (Nat.pow_le_pow_right (by omega) (by omega)))]; rfl
def segGood (w o : ℕ) (s : ℕ × ℕ) : Bool :=
  Nat.beq ((w >>> (o + s.1 + 1)) % 2 ^ (s.2 - s.1 - 1)) 0 || Nat.beq ((w >>> (o + s.1 + 1)) % 2 ^ (s.2 - s.1 - 1)) (2 ^ (s.2 - s.1 - 1) - 1)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma raw_good : rawG.all (fun w => segsX.all (segGood w 0) && segsY.all (segGood w NN)) = true := by decide +kernel
lemma segGood_eq {w o : ℕ} {s : ℕ × ℕ} (h : segGood w o s = true) {i j : ℕ} (h1 : s.1 < i) (h2 : i < s.2) (h3 : s.1 < j) (h4 : j < s.2) :
    w.testBit (o + i) = w.testBit (o + j) := by
  have key : ∀ i, s.1 < i → i < s.2 → w.testBit (o + i) = ((w >>> (o + s.1 + 1)) % 2 ^ (s.2 - s.1 - 1)).testBit (i - s.1 - 1) := by
    intro i h1 h2
    rw [Nat.testBit_mod_two_pow, Nat.testBit_shiftRight, show o + s.1 + 1 + (i - s.1 - 1) = o + i by omega]
    simp [show i - s.1 - 1 < s.2 - s.1 - 1 by omega]
  rw [key i h1 h2, key j h3 h4]
  simp only [segGood, Bool.or_eq_true, Nat.beq_eq] at h
  rcases h with h | h <;> rw [h]
  · simp
  · rw [Nat.testBit_two_pow_sub_one, Nat.testBit_two_pow_sub_one]
    simp [show i - s.1 - 1 < s.2 - s.1 - 1 by omega, show j - s.1 - 1 < s.2 - s.1 - 1 by omega]
lemma wire_good {w : ℕ} (hw : w ∈ rawG) (Z : ℕ) : Good (lz Z) (w &&& mz Z) := by
  have h := List.all_eq_true.1 raw_good w hw
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  refine ⟨fun i j hij h1 h2 => ?_, fun i j hij h1 h2 => ?_⟩ <;> obtain ⟨s, hs, a1, a2, a3, a4⟩ := hij
  · have := segGood_eq (h.1 s hs) a1 a2 a3 a4
    simp only [Nat.zero_add] at this
    rw [Nat.testBit_and, Nat.testBit_and, this, (lz_lg Z i h1).1.1, (lz_lg Z j h2).1.1]
  · have := segGood_eq (h.2 s hs) a1 a2 a3 a4
    rw [Nat.testBit_and, Nat.testBit_and, this, (lz_lg Z i h1).1.2.1, (lz_lg Z j h2).1.2.1]
noncomputable section
def pL (L : List ℕ) : ℕ := List.rec (motive := fun _ => ℕ) 0 (fun d _ ih => Nat.add (Nat.shiftLeft ih 5) d) L
end
lemma pL_cons (d : ℕ) (L : List ℕ) : pL (d :: L) = 2 ^ 5 * pL L + d := by
  change (pL L <<< 5) + d = _; rw [Nat.shiftLeft_eq]; ring
lemma pL_pk (L : List ℕ) : pL L = pk L.length (fun j => L.getD j 0) := by
  induction L with
  | nil => simp [pL, pk]
  | cons d L ih =>
    rw [pL_cons, ih, pk, pk, List.length_cons, Finset.sum_range_succ', Finset.mul_sum]
    simp only [Nat.mul_zero, pow_zero, mul_one, List.getD_cons_zero, List.getD_cons_succ]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show 5 * (j + 1) = 5 * j + 5 by ring, pow_add]; ring
lemma pL_bit {L : List ℕ} (h : ∀ d ∈ L, d ≤ 1) : ∀ i, (pL L).testBit i = true ↔ (i % 5 = 0 ∧ i / 5 < L.length ∧ L.getD (i / 5) 0 = 1) := by
  induction L with
  | nil => intro i; simp [pL]
  | cons d L ih =>
    intro i
    have hd := h d (by simp)
    have ih := ih fun x hx => h x (by simp [hx])
    rw [pL_cons, Nat.testBit_two_pow_mul_add _ (by omega)]
    split_ifs with hi
    · have : i / 5 = 0 := by omega
      rw [this]
      rcases Nat.eq_zero_or_pos i with rfl | hp
      · interval_cases d <;> simp
      · constructor
        · intro hb
          have : d.testBit i = false := Nat.testBit_lt_two_pow (lt_of_le_of_lt hd (Nat.one_lt_two_pow (by omega)))
          rw [this] at hb; simp at hb
        · intro hb; omega
    · rw [ih, show i / 5 = (i - 5) / 5 + 1 by omega]
      simp only [List.length_cons, List.getD_cons_succ]
      constructor
      · rintro ⟨a, b, c⟩; exact ⟨by omega, by omega, c⟩
      · rintro ⟨a, b, c⟩; exact ⟨by omega, by omega, c⟩
lemma pL_isPk {L : List ℕ} (h : ∀ d ∈ L, d ≤ 1) : isPk L.length (pL L) := fun i hi => by
  have := (pL_bit h i).1 hi; exact ⟨this.1, this.2.1⟩
def bit01 (b : Bool) : ℕ := bif b then 1 else 0
def mkW (P : List ℕ) (s : ℕ) : W := ⟨s, pL (P.map fun n => bit01 (Nat.beq (Nat.land s n) 0)), pL (P.map fun n => bit01 (Nat.beq (Nat.land s n) n)),
  Nat.lor (pL (P.map fun n => bit01 (Nat.beq (Nat.land s n) 0))) (pL (P.map fun n => bit01 (Nat.beq (Nat.land s n) n))), 3⟩
lemma mkW_ok (P : List ℕ) (s : ℕ) : WOk P (mkW P s) := by
  have h01 : ∀ f : ℕ → Bool, ∀ d ∈ P.map (fun n => bit01 (f n)), d ≤ 1 := by
    intro f d hd; simp only [List.mem_map] at hd
    obtain ⟨n, _, rfl⟩ := hd; cases f n <;> simp [bit01]
  have bt : ∀ f : ℕ → Bool, ∀ j < P.length, (pL (P.map fun n => bit01 (f n))).testBit (5 * j) = true → f (P.getD j 0) = true := by
    intro f j hj h
    have h := ((pL_bit (h01 f) _).1 h).2.2
    rw [show 5 * j / 5 = j by omega, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hj] at h
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
    simp at h ⊢
    cases hf : f P[j] <;> simp [bit01, hf] at h ⊢
  refine ⟨?_, ?_, rfl, fun j hj h => ?_, fun j hj h => ?_⟩
  · have := pL_isPk (h01 fun n => Nat.beq (Nat.land s n) 0); rwa [List.length_map] at this
  · have := pL_isPk (h01 fun n => Nat.beq (Nat.land s n) n); rwa [List.length_map] at this
  · exact Nat.eq_of_beq_eq_true (bt (fun n => Nat.beq (Nat.land s n) 0) j hj h)
  · exact Nat.eq_of_beq_eq_true (bt (fun n => Nat.beq (Nat.land s n) n) j hj h)
noncomputable section
def addS (o : W) (v : List W) : List W := List.rec (motive := fun _ => List W) [o]
  (fun w t ih => Bool.rec (motive := fun _ => List W) (w :: ih) (Bool.rec (motive := fun _ => List W) (o :: w :: t) (w :: t) (Nat.beq o.s w.s)) (Nat.ble w.s o.s)) v
def avl (P : List ℕ) (m : ℕ) (L : List ℕ) : List W := List.rec (motive := fun _ => List W) []
  (fun w _ ih => Bool.rec (motive := fun _ => List W) (Bool.rec (motive := fun _ => List W) (addS (mkW P (Nat.land w m)) ih) ih (Nat.beq (Nat.land w m) m)) ih (Nat.beq (Nat.land w m) 0)) L
def frc (v : List W) : (List W → Bool) → Bool := List.rec (motive := fun _ => (List W → Bool) → Bool) (fun h => h [])
  (fun w _ ih h => st w.s fun s => st w.a fun a => st w.b fun b => st w.c fun c => ih fun r => h (⟨s, a, b, c, w.r⟩ :: r)) v
def anySub (d : Bool) (l : ℕ) (v : List W) : ℕ → (List W → Bool) → Bool := List.rec (motive := fun _ => ℕ → (List W → Bool) → Bool) (fun _ h => h [])
  (fun w t ih c h => Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) false (ih c h) (Nat.beq (Nat.lor c (cov d l t)) l)) true
    (st (Nat.lor c (sp d l w.s)) fun c => ih c fun r => h (w :: r))) v
def sumc (v : List W) : ℕ := List.rec (motive := fun _ => ℕ) 0 (fun w _ ih => Nat.add w.c ih) v
def MM : ℕ := 214
def hb (H x : ℕ) : Bool := Nat.beq (Nat.land (Nat.shiftRight H (Nat.mod x MM)) 1) 1
def pairsC (H : ℕ) (h : X → X → Bool) (xs : List X) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun a r ih => Bool.rec (motive := fun _ => Bool) ih true
    (scan (fun x => Bool.rec (motive := fun _ => Bool) false (h a x) (hb H (Nat.add a.s x.s))) r)) xs
def topC (l m g K H ph k t z : ℕ) (v : List W) : Bool :=
  Bool.rec (motive := fun _ => Bool) (tst (pos t) l (Nat.sub (Nat.succ k) t) v (fun y =>
    Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) false (mv (look l m g K) l m g k t z v y) (Nat.beq ph 1)) true
      (node (look1 l m g K K (Nat.sub k 1) t) (pos t) l m g (Nat.sub (Nat.sub k t) y) v.length z v (fun h xs => pairsC H h (fs xs))))) true (Nat.ble v.length 1)
def hasP (p : ℕ) (v : List W) : Bool := Bool.rec (motive := fun _ => Bool)
  (List.rec (motive := fun _ => Bool) false (fun w _ ih => Bool.rec (motive := fun _ => Bool) ih true (Nat.beq w.s p)) v) true (Nat.beq p 0)
def startv (l m g B K t p H ph : ℕ) (v : List W) : Bool :=
  Bool.rec (motive := fun _ => Bool) false (Bool.rec (motive := fun _ => Bool) false
    (child (fun z r => topC l m g K H ph K t z r) g (fun h => h v) (Nat.sub B (sumc v)))
    (Nat.ble v.length (Nat.sub (Nat.succ K) t))) (hasP p v)
end
lemma frc_eq (v : List W) : ∀ h, frc v h = h v := by
  induction v with
  | nil => intro h; rfl
  | cons w v ih =>
    intro h
    change st w.s (fun s => st w.a fun a => st w.b fun b => st w.c fun c => frc v fun r => h (⟨s, a, b, c, w.r⟩ :: r)) = _
    simp only [st_eq]; rw [ih]
lemma anySub_false {d : Bool} {l : ℕ} {v : List W} : ∀ {c : ℕ} {h : List W → Bool}, (∀ i, c.testBit i = true → l.testBit i = true) → anySub d l v c h = false →
    ∀ r, r.Sublist v → (∀ i, l.testBit i = true → c.testBit i = true ∨ (cov d l r).testBit i = true) → h r = false := by
  induction v with
  | nil => intro c h _ hh r hr _; rw [List.sublist_nil.1 hr]; exact hh
  | cons w v ih =>
    intro c h hcl hh r hr hcov
    change (Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) false (anySub d l v c h) (Nat.beq (Nat.lor c (cov d l v)) l)) true
      (st (Nat.lor c (sp d l w.s)) fun c => anySub d l v c fun r => h (w :: r)) : Bool) = false at hh
    rw [bR, bR, st_eq] at hh
    cases h1 : anySub d l v (Nat.lor c (sp d l w.s)) (fun r => h (w :: r)) with
    | true => rw [h1] at hh; simp at hh
    | false =>
      rw [h1, Bool.cond_false] at hh
      have hc2 : ∀ i, (cov d l v).testBit i = true → l.testBit i = true := by
        intro i hi
        obtain ⟨w', _, hw'⟩ := (cov_bit _ _ _ _).1 hi
        rw [sp_bit, Bool.and_eq_true] at hw'; exact hw'.1
      cases hr with
      | cons _ hr =>
        have : Nat.beq (Nat.lor c (cov d l v)) l = true := by
          rw [Nat.beq_eq]
          apply Nat.eq_of_testBit_eq; intro i
          rw [no, Nat.testBit_or]
          cases hli : l.testBit i with
          | false =>
            by_contra hc
            rw [Bool.not_eq_false, Bool.or_eq_true] at hc
            rcases hc with h | h
            · rw [hcl i h] at hli; simp at hli
            · rw [hc2 i h] at hli; simp at hli
          | true =>
            rcases hcov i hli with h | h
            · rw [h]; rfl
            · obtain ⟨w', hw', h2⟩ := (cov_bit _ _ _ _).1 h
              rw [(cov_bit d l i v).2 ⟨w', hr.subset hw', h2⟩]; simp
        rw [this, Bool.cond_true] at hh
        exact ih hcl hh r hr hcov
      | cons_cons _ hr =>
        rename_i r'
        refine ih (c := Nat.lor c (sp d l w.s)) ?_ h1 r' hr ?_
        · intro i hi
          rw [no, Nat.testBit_or, Bool.or_eq_true] at hi
          rcases hi with h | h
          · exact hcl i h
          · rw [sp_bit, Bool.and_eq_true] at h; exact h.1
        · intro i hi
          rw [no, Nat.testBit_or, Bool.or_eq_true]
          rcases hcov i hi with h | h
          · exact Or.inl (Or.inl h)
          · change (Nat.lor (sp d l w.s) (cov d l r')).testBit i = true at h
            rw [no, Nat.testBit_or, Bool.or_eq_true] at h
            rcases h with h | h
            · exact Or.inl (Or.inr h)
            · exact Or.inr h
lemma addS_cons (o w : W) (t : List W) : addS o (w :: t) = bif Nat.ble w.s o.s then (bif Nat.beq o.s w.s then w :: t else o :: w :: t) else w :: addS o t := by
  change Bool.rec (motive := fun _ => List W) (w :: addS o t) (Bool.rec (motive := fun _ => List W) (o :: w :: t) (w :: t) (Nat.beq o.s w.s)) (Nat.ble w.s o.s) = _
  cases Nat.ble w.s o.s <;> cases Nat.beq o.s w.s <;> rfl
def Srt (v : List W) : Prop := v.Pairwise (fun a b => b.s < a.s)
lemma addS_spec {o : W} {v : List W} (hv : Srt v) : Srt (addS o v) ∧ (∀ w ∈ addS o v, w = o ∨ w ∈ v) ∧
    (∃ w ∈ addS o v, w.s = o.s) ∧ ∀ w ∈ v, w ∈ addS o v := by
  induction v with
  | nil => exact ⟨List.pairwise_singleton _ _, by simp [addS], ⟨o, by simp [addS], rfl⟩, by simp⟩
  | cons x t ih =>
    have hp := List.pairwise_cons.1 hv
    obtain ⟨i1, i2, i3, i4⟩ := ih hp.2
    rw [addS_cons]
    cases h1 : Nat.ble x.s o.s with
    | true =>
      have hle := Nat.le_of_ble_eq_true h1
      cases h2 : Nat.beq o.s x.s with
      | true => exact ⟨hv, fun w hw => Or.inr hw, ⟨x, by simp, (Nat.eq_of_beq_eq_true h2).symm⟩, fun w hw => hw⟩
      | false =>
        have hne : o.s ≠ x.s := fun e => by rw [e, Nat.beq_refl] at h2; simp at h2
        refine ⟨List.pairwise_cons.2 ⟨fun w hw => ?_, hv⟩, fun w hw => by simpa using hw, ⟨o, by simp, rfl⟩, fun w hw => by simp at hw ⊢; tauto⟩
        simp only [List.mem_cons] at hw
        rcases hw with rfl | hw
        · omega
        · have := hp.1 w hw; omega
    | false =>
      have hlt : o.s < x.s := by
        by_contra hc; rw [Nat.ble_eq_true_of_le (by omega)] at h1; simp at h1
      refine ⟨List.pairwise_cons.2 ⟨fun w hw => ?_, i1⟩, fun w hw => ?_, ?_, fun w hw => ?_⟩
      · rcases i2 w hw with rfl | h
        · exact hlt
        · exact hp.1 w h
      · simp only [Bool.cond_false, List.mem_cons] at hw ⊢
        rcases hw with rfl | hw
        · simp
        · rcases i2 w hw with h | h <;> simp [h]
      · obtain ⟨w, hw, e⟩ := i3; exact ⟨w, by simp [hw], e⟩
      · simp only [Bool.cond_false, List.mem_cons] at hw ⊢
        rcases hw with rfl | hw
        · simp
        · exact Or.inr (i4 w hw)
lemma avl_spec (P : List ℕ) (m : ℕ) (L : List ℕ) : Srt (avl P m L) ∧ (∀ w ∈ avl P m L, ∃ x ∈ L, w = mkW P (x &&& m)) ∧
    ∀ x ∈ L, x &&& m ≠ 0 → x &&& m ≠ m → ∃ w ∈ avl P m L, w.s = x &&& m := by
  induction L with
  | nil => exact ⟨List.Pairwise.nil, by simp [avl], by simp⟩
  | cons y L ih =>
    obtain ⟨i1, i2, i3⟩ := ih
    have e : avl P m (y :: L) = bif Nat.beq (Nat.land y m) 0 then avl P m L else bif Nat.beq (Nat.land y m) m then avl P m L else addS (mkW P (Nat.land y m)) (avl P m L) := by
      change Bool.rec (motive := fun _ => List W) (Bool.rec (motive := fun _ => List W) (addS (mkW P (Nat.land y m)) (avl P m L)) (avl P m L) (Nat.beq (Nat.land y m) m)) (avl P m L) (Nat.beq (Nat.land y m) 0) = _
      cases Nat.beq (Nat.land y m) 0 <;> cases Nat.beq (Nat.land y m) m <;> rfl
    have old : ∀ w ∈ avl P m L, ∃ x ∈ y :: L, w = mkW P (x &&& m) := fun w hw => by
      obtain ⟨x, hx, e⟩ := i2 w hw; exact ⟨x, by simp [hx], e⟩
    rw [e]
    cases h1 : Nat.beq (Nat.land y m) 0 with
    | true =>
      refine ⟨i1, old, fun x hx h2 h3 => ?_⟩
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact absurd (Nat.eq_of_beq_eq_true h1) h2
      · exact i3 x hx h2 h3
    | false =>
      cases h1' : Nat.beq (Nat.land y m) m with
      | true =>
        refine ⟨i1, old, fun x hx h2 h3 => ?_⟩
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact absurd (Nat.eq_of_beq_eq_true h1') h3
        · exact i3 x hx h2 h3
      | false =>
        obtain ⟨j1, j2, j3, j4⟩ := addS_spec (o := mkW P (Nat.land y m)) i1
        refine ⟨j1, fun w hw => ?_, fun x hx h2 h3 => ?_⟩
        · rcases j2 w hw with rfl | h
          · exact ⟨y, by simp, rfl⟩
          · exact old w h
        · simp only [List.mem_cons] at hx
          rcases hx with rfl | hx
          · exact j3
          · obtain ⟨w, hw, e⟩ := i3 x hx h2 h3; exact ⟨w, j4 w hw, e⟩
lemma pairsC_false {H : ℕ} {h : X → X → Bool} {xs : List X} (hp : pairsC H h xs = false) :
    xs.Pairwise (fun a b => hb H (a.s + b.s) = true → h a b = false) := by
  induction xs with
  | nil => simp
  | cons a r ih =>
    change (Bool.rec (motive := fun _ => Bool) (pairsC H h r) true
      (scan (fun x => Bool.rec (motive := fun _ => Bool) false (h a x) (hb H (Nat.add a.s x.s))) r) : Bool) = false at hp
    rw [bR] at hp
    rw [List.pairwise_cons]
    constructor
    · intro b hbm hi
      have h1 : scan (fun x => Bool.rec (motive := fun _ => Bool) false (h a x) (hb H (Nat.add a.s x.s))) r = false := by
        revert hp
        cases scan (fun x => Bool.rec (motive := fun _ => Bool) false (h a x) (hb H (Nat.add a.s x.s))) r <;> simp
      have h2 := scan_false h1 b hbm
      beta_reduce at h2
      rw [bR] at h2
      have h3 : hb H (Nat.add a.s b.s) = true := hi
      rwa [h3, Bool.cond_true] at h2
    · apply ih; revert hp; cases pairsC H h r <;> simp
def mFull (M : List (ℕ × ℕ)) : Bool := (List.range MM).all (fun r => M.any (fun p => hb p.1 r)) && M.any (fun p => Nat.beq p.2 1)
lemma hb_mod (H x : ℕ) : hb H x = hb H (x % MM) := by
  unfold hb
  change Nat.beq ((H >>> (x % MM)) &&& 1) 1 = Nat.beq ((H >>> (x % MM % MM)) &&& 1) 1
  rw [Nat.mod_mod]
section sound
variable {P : List ℕ} {l m g T : ℕ} (X : Ctx P l m g T)
include X
lemma topC_sound (hR : RR R) (hR2 : ∀ d a b, (R a = 0 ∨ R b = 0) → Al R d a b) {K k t z : ℕ} {v : List W} {S : Finset ℕ} {M : List (ℕ × ℕ)}
    (hM : mFull M = true) (h : ∀ p ∈ M, topC l m g K p.1 p.2 k t z v = false) (hs : StOk P T l k z v S) (hcod : ∀ w ∈ v, w.r = R w.s)
    {k' : ℕ} (hk : k' ≤ k) (hl : Live Z0 m T k' t S) (hmW : ∀ q < k', ¬ Sol Z0 m T q (C m ({x | R x ≠ 0} ∪ (S : Set ℕ)))) : False := by
  simp only [mFull, Bool.and_eq_true, List.all_eq_true, List.mem_range, List.any_eq_true] at hM
  obtain ⟨hM1, p0, hp0, hp1⟩ := hM
  have un : ∀ p ∈ M, 2 ≤ v.length ∧ tst (pos' t) l (k + 1 - t) v (fun y =>
      Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) false (mv (look l m g K) l m g k t z v y) (Nat.beq p.2 1)) true
      (node (look1 l m g K K (k - 1) t) (pos' t) l m g (k - t - y) v.length z v (fun h xs => pairsC p.1 h (fs xs)))) = false := by
    intro p hp
    have h := h p hp
    change (Bool.rec (motive := fun _ => Bool) (tst (pos t) l (k + 1 - t) v (fun y =>
      Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) false (mv (look l m g K) l m g k t z v y) (Nat.beq p.2 1)) true
      (node (look1 l m g K K (k - 1) t) (pos t) l m g (k - t - y) v.length z v (fun h xs => pairsC p.1 h (fs xs))))) true (Nat.ble v.length 1) : Bool) = false at h
    rw [bR, pos_eq] at h
    cases h0 : Nat.ble v.length 1 with
    | true => rw [h0] at h; simp at h
    | false =>
      rw [h0, cond_false] at h
      refine ⟨?_, h⟩
      by_contra hc
      rw [Nat.ble_eq_true_of_le (by omega)] at h0; simp at h0
  have hmin : Min Z0 m T k' t S := ⟨hl, fun q hq hs => hmW q hq (hs.mono le_rfl (C_mono Set.subset_union_right))⟩
  obtain ⟨y, hFy, hyk⟩ := tst_sound X hs hmin hk
  have un2 := fun p hp => (hFy _).symm.trans (un p hp).2
  refine one_sound X hR hR2 (K := K) (f := look1 l m g K K) (look1_sound X hR hR2 (K := K) K) hs hcod (un p0 hp0).1 hk hl hmW hyk ?_ ?_
  · have := (or_false' X (un2 p0 hp0)).2
    rw [bR, hp1, cond_true] at this; exact this
  · intro a ha c hc hne har hcr
    obtain ⟨p, hpM, hpb⟩ := hM1 ((a.s + c.s) % MM) (Nat.mod_lt _ (by decide))
    rw [← hb_mod] at hpb
    refine ⟨_, (or_false' X (un2 p hpM)).1, fun h hp => ?_⟩
    have hpw := pairsC_false hp
    have : Std.Symm (fun a b : L_meta_11040.X => hb p.1 (a.s + b.s) = true → (h a b = false ∨ h b a = false)) :=
      ⟨fun a b h e => (h (by rw [Nat.add_comm]; exact e)).symm⟩
    exact (hpw.imp (S := fun a b => hb p.1 (a.s + b.s) = true → (h a b = false ∨ h b a = false)) fun h e => Or.inl (h e)).forall
      (fs_mem (List.mem_map_of_mem ha) har) (fs_mem (List.mem_map_of_mem hc) hcr) (fun e => hne (congrArg L_meta_11040.X.s e)) hpb
end sound
def WZ (E : List (ℕ × ℕ)) (Z : ℕ) : Set ℕ := {x | ∃ w ∈ rawL E, x = w &&& mz Z}
def Imp (E : List (ℕ × ℕ)) (Z L : ℕ) : Prop := ∀ q < L, ¬ Sol Z0 (mz Z) (tz Z) q (C (mz Z) (WZ E Z))
def PZ (Q : List (ℕ × ℕ)) : List ℕ := Q.map (fun e => mz e.1)
def pOk (Z : ℕ) (Q : List (ℕ × ℕ)) : Bool := !Nat.beq (tz Z) 0 && !Nat.beq (tz Z) (mz Z) && Q.all (fun e => Nat.beq (Nat.land (mz e.1) (mz Z)) (mz e.1) &&
  !Nat.beq (tz e.1) 0 && !Nat.beq (tz e.1) (mz e.1))
def pwr (E : List (ℕ × ℕ)) (Z : ℕ) : ℕ := (E.map fun e => Nat.land (xw e) (mz Z)).headD 0
noncomputable def chk (E Q : List (ℕ × ℕ)) (Z K t H ph : ℕ) : Bool :=
  (fun l => (fun m => (fun P => (fun g => (fun B => (fun p =>
    frc (avl P m (rawL E)) (fun v => st l fun l => st m fun m => st g fun g => st B fun B => st p fun p =>
      anySub (pos t) l v 0 (fun r => startv l m g B K t p H ph r)))
    (pwr E Z)) (pL (Q.map fun e => 16 + (K - e.2)))) (pL (Q.map fun _ => 16))) (PZ Q)) (mz Z)) (lz Z)
lemma tz_sub {Z Z' : ℕ} (h : mz Z' &&& mz Z = mz Z') : tz Z &&& mz Z' = tz Z' := by
  simp only [tz, nl, Nat.and_assoc]; rw [Nat.and_comm (mz Z), h]
lemma Im_WZ {E : List (ℕ × ℕ)} {Z Z' : ℕ} (h : mz Z' &&& mz Z = mz Z') {S : Finset ℕ} (hS : (S : Set ℕ) ⊆ WZ E Z) : Im (mz Z') S ⊆ WZ E Z' := by
  rintro x ⟨y, hy, rfl⟩
  obtain ⟨w, hw, rfl⟩ := hS hy
  exact ⟨w, hw, by simp only [Nat.and_assoc]; rw [Nat.and_comm (mz Z), h]⟩
lemma sumc_eq {P : List ℕ} {v : List W} (hw : ∀ w ∈ v, WOk P w) : sumc v = pk P.length (cnt v) := by
  induction v with
  | nil => simp [sumc, pk, cnt]
  | cons w v ih =>
    change w.c + sumc v = _
    rw [ih fun x hx => hw x (by simp [hx]), fl_pk (hw w (by simp)), pk_add]
    exact pk_congr fun j _ => by rw [cnt_cons]
lemma pk16 (Q : List (ℕ × ℕ)) (K : ℕ) : pL (Q.map fun e => 16 + (K - e.2)) = pk (PZ Q).length (fun j => 16 + (K - (Q.getD j (0, K)).2)) := by
  rw [pL_pk, PZ, List.length_map, List.length_map]
  refine pk_congr fun j hj => ?_
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hj]; rfl
open Classical in
noncomputable def RZ (E : List (ℕ × ℕ)) (Z : ℕ) : ℕ → ℕ := fun s => if s ∈ WZ E Z then 3 else 0
lemma RZ_set (E : List (ℕ × ℕ)) (Z : ℕ) : {x | RZ E Z x ≠ 0} = WZ E Z := by
  ext x; simp only [RZ, Set.mem_setOf_eq]; split_ifs with h <;> simp [h]
lemma RZ_R (E : List (ℕ × ℕ)) (Z : ℕ) : RR (RZ E Z) := by
  intro d a b ha hb h
  have h3 : ∀ x, RZ E Z x ≠ 0 → RZ E Z x = 3 := by
    intro x hx; unfold RZ at hx ⊢; split_ifs at hx ⊢ with h
    · rfl
    · simp at hx
  unfold Al at h
  rw [h3 a ha, h3 b hb] at h
  cases d <;> simp at h
lemma RZ_R2 (E : List (ℕ × ℕ)) (Z : ℕ) : ∀ d a b, (RZ E Z a = 0 ∨ RZ E Z b = 0) → Al (RZ E Z) d a b := by
  intro d a b h
  unfold Al
  rcases h with h | h <;> rw [h] <;> simp
lemma hasP_ok {p : ℕ} {v : List W} (h : p = 0 ∨ ∃ w ∈ v, w.s = p) : hasP p v = true := by
  unfold hasP
  rw [bR]
  rcases h with rfl | ⟨w, hw, rfl⟩
  · rfl
  · have : (List.rec (motive := fun _ => Bool) false (fun w' _ ih => Bool.rec (motive := fun _ => Bool) ih true (Nat.beq w'.s w.s)) v : Bool) = true := by
      induction v with
      | nil => simp at hw
      | cons x v ih =>
        change (Bool.rec (motive := fun _ => Bool) (List.rec (motive := fun _ => Bool) false (fun w' _ ih => Bool.rec (motive := fun _ => Bool) ih true (Nat.beq w'.s w.s)) v : Bool) true (Nat.beq x.s w.s) : Bool) = true
        rw [bR]
        simp only [List.mem_cons] at hw
        rcases hw with rfl | hw
        · rw [Nat.beq_refl]; rfl
        · rw [ih hw]; cases Nat.beq x.s w.s <;> rfl
    rw [this]; cases Nat.beq w.s 0 <;> rfl
lemma rawL_sub {E : List (ℕ × ℕ)} (hE : ∀ e ∈ E, e ∈ six) {w : ℕ} (hw : w ∈ rawL E) : w ∈ rawG := by
  simp only [rawG, rawL, List.mem_append, List.mem_map] at hw ⊢
  rcases hw with h | ⟨e, he, rfl⟩
  · exact Or.inl h
  · exact Or.inr ⟨e, hE e he, rfl⟩
theorem imp_of {E Q : List (ℕ × ℕ)} {Z L : ℕ} (hE : E = [] ∨ ∃ e ∈ six, E = [e] ∧ Imp [] Z L) (hp : pOk Z Q = true) (hL : L ≤ 16) (hI : ∀ e ∈ Q, Imp E e.1 e.2)
    (hb : (∃ e ∈ Q, L ≤ e.2) ∨ ∀ t < L, ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ p ∈ M, chk E Q Z (L - 1) t p.1 p.2 = false) : Imp E Z L := by
  intro q hq hsol
  simp only [pOk, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true] at hp
  obtain ⟨⟨hp0, hp1⟩, hp2⟩ := hp
  have nb : ∀ {x y : ℕ}, Nat.beq x y = false → x ≠ y := fun h e => by rw [e, Nat.beq_refl] at h; simp at h
  have hT : tz Z &&& mz Z = tz Z := by simp only [tz, nl, Nat.and_assoc, Nat.and_self]
  have hE6 : ∀ e ∈ E, e ∈ six := by
    rcases hE with rfl | ⟨e, he, rfl, _⟩
    · simp
    · intro e' he'; simp only [List.mem_singleton] at he'; rw [he']; exact he
  classical
  have hex : ∃ q, Sol Z0 (mz Z) (tz Z) q (C (mz Z) (WZ E Z)) := ⟨q, hsol⟩
  have hqL : Nat.find hex < L := lt_of_le_of_lt (Nat.find_min' hex hsol) hq
  obtain ⟨k, hk, t, S, hS, hl⟩ := (Nat.find_spec hex).live
  have hCS : C (mz Z) (S : Set ℕ) ⊆ C (mz Z) (WZ E Z) := by
    rintro x (hx | hx)
    · exact hS hx
    · exact Or.inr hx
  have hkeq : k = Nat.find hex := le_antisymm hk (Nat.find_min' hex (hl.sol.mono le_rfl hS))
  have hm : Min Z0 (mz Z) (tz Z) k t S := ⟨hl, fun q' hq' hs => Nat.find_min hex (by omega) (hs.mono le_rfl hCS)⟩
  have hbd : ∀ x ∈ S, x &&& mz Z = x := by
    intro x hx
    rcases hS hx with ⟨w, _, rfl⟩ | h
    · rw [Nat.and_assoc, Nat.and_self]
    · simp at h; rcases h with rfl | rfl <;> simp
  obtain ⟨h0, h1⟩ := hm.proper hT (nb hp0) (nb hp1) hbd
  have hSW : (S : Set ℕ) ⊆ WZ E Z := by
    intro x hx
    rcases hS hx with h | h
    · exact h
    · simp at h; rcases h with rfl | rfl
      · exact absurd hx h0
      · exact absurd hx h1
  have hproj : ∀ e ∈ Q, mz e.1 &&& mz Z = mz e.1 ∧ tz e.1 ≠ 0 ∧ tz e.1 ≠ mz e.1 := by
    intro e he
    obtain ⟨⟨a, b⟩, c⟩ := hp2 e he
    exact ⟨Nat.eq_of_beq_eq_true a, nb b, nb c⟩
  have hno : ∀ e ∈ Q, ∀ q < e.2, ¬ Sol Z0 (mz e.1) (tz Z &&& mz e.1) q (C (mz e.1) (Im (mz e.1) S)) := by
    intro e he q hq hs
    have h3 := (hproj e he).1
    rw [tz_sub h3] at hs
    exact hI e he q hq (hs.mono le_rfl (C_mono (Im_WZ h3 hSW)))
  have htk := hm.size.2
  rcases hb with ⟨e, he, hle⟩ | hb
  · have h3 := hproj e he
    obtain ⟨q', hq', hs'⟩ := hm.const h3.1 (by rw [tz_sub h3.1]; exact h3.2.1) (by rw [tz_sub h3.1]; exact h3.2.2)
    exact hno e he q' (by omega) hs'
  have hpw : pwr E Z = 0 ∨ pwr E Z ∈ S := by
    rcases hE with rfl | ⟨e, he, rfl, hraw⟩
    · exact Or.inl rfl
    · by_contra hc
      push Not at hc
      refine hraw k (by omega) (hl.sol.mono le_rfl ?_)
      intro x hx
      obtain ⟨w, hw, rfl⟩ := hSW hx
      simp only [rawL, List.mem_append, List.map_cons, List.map_nil, List.mem_singleton] at hw
      rcases hw with hw | rfl
      · exact Or.inl ⟨w, by simp [rawL, hw], rfl⟩
      · have hx : xw e &&& mz Z ∈ S := by simpa using hx
        exact absurd (show pwr [e] Z ∈ S from hx) hc.2
  obtain ⟨M, hMf, hchk⟩ := hb t (by omega)
  obtain ⟨a1, a2, a3⟩ := avl_spec (PZ Q) (mz Z) (rawL E)
  set v := (avl (PZ Q) (mz Z) (rawL E)).filter (fun w => decide (w.s ∈ S)) with hv
  have hsub : v.Sublist (avl (PZ Q) (mz Z) (rawL E)) := List.filter_sublist
  have hnd : (v.map W.s).Nodup := by
    rw [List.Nodup, List.pairwise_map]
    exact (a1.sublist hsub).imp fun h => Nat.ne_of_gt h
  have hrep : Rep v S := by
    refine ⟨hnd, Finset.ext fun x => ?_⟩
    rw [List.mem_toFinset, List.mem_map]
    constructor
    · rintro ⟨w, hw, rfl⟩
      rw [hv, List.mem_filter] at hw; simpa using hw.2
    · intro hx
      obtain ⟨w, hw, rfl⟩ := hSW hx
      obtain ⟨w', hw', e⟩ := a3 w hw (fun e => h0 (e ▸ hx)) (fun e => h1 (e ▸ hx))
      exact ⟨w', by rw [hv, List.mem_filter]; exact ⟨hw', by simpa [e] using hx⟩, e⟩
  have hwok : ∀ w ∈ v, WOk (PZ Q) w := by
    intro w hw
    obtain ⟨x, _, rfl⟩ := a2 w (hsub.subset hw); exact mkW_ok _ _
  have hcod : ∀ w ∈ v, w.r = RZ E Z w.s := by
    intro w hw
    obtain ⟨x, hx, rfl⟩ := a2 w (hsub.subset hw)
    have : x &&& mz Z ∈ WZ E Z := ⟨x, hx, rfl⟩
    change 3 = RZ E Z (x &&& mz Z)
    rw [RZ, if_pos this]
  have hgood : ∀ w ∈ v, Good (lz Z) w.s := by
    intro w hw
    obtain ⟨x, hx, rfl⟩ := a2 w (hsub.subset hw); exact wire_good (rawL_sub hE6 hx) Z
  have hPlen : (PZ Q).length = Q.length := by simp [PZ]
  have hPget : ∀ j < (PZ Q).length, (PZ Q).getD j 0 = mz (Q.getD j (0, L - 1)).1 ∧ Q.getD j (0, L - 1) ∈ Q := by
    intro j hj
    rw [hPlen] at hj
    simp [PZ, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hj]
  have X : Ctx (PZ Q) (lz Z) (mz Z) (pL (Q.map fun _ => 16)) (tz Z) := by
    refine ⟨fun i hi => lz_lg Z i hi, fun j hj => ?_, ?_⟩
    · obtain ⟨e1, e2⟩ := hPget j hj
      have h3 := hproj _ e2
      rw [e1, tz_sub h3.1]; exact h3
    · rw [pL_pk, List.length_map, hPlen]
      refine pk_congr fun j hj => ?_
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hj]; rfl
  have hcl : Cl (PZ Q) (tz Z) (L - 1) (fun j => L - 1 - (Q.getD j (0, L - 1)).2) S := by
    intro j hj q hq
    obtain ⟨e1, e2⟩ := hPget j hj
    have hq' : q + (L - 1 - (Q.getD j (0, L - 1)).2) < L - 1 := hq
    rw [e1]; exact hno _ e2 q (by omega)
  have hle := cnt_le X hrep hwok hcl hm (by omega)
  have hst : StOk (PZ Q) (tz Z) (lz Z) (L - 1) (pL (Q.map fun e => 16 + (L - 1 - e.2)) - sumc v) v S := by
    refine ⟨hrep, hwok, hgood, _, fun j _ => by omega, hcl, ?_⟩
    rw [sumc_eq hwok, pk16, pk_sub]
    intro j hj; have := hle j hj; omega
  have hcov : ∀ i, (lz Z).testBit i = true → (0 : ℕ).testBit i = true ∨ (cov (pos t) (lz Z) v).testBit i = true := by
    intro i hli
    right
    rw [cov_bit]
    obtain ⟨⟨m1, m2, t1, t2⟩, _⟩ := lz_lg Z i hli
    obtain ⟨w, hw, hs⟩ := hl.cov m1 m2 t1 t2
    obtain ⟨w', hw', rfl⟩ := hrep.mem.1 hw
    exact ⟨w', hw', by rw [sp_bit, hli, pos_eq, hs]; rfl⟩
  have hsz := hm.size.1
  have hcard := hrep.card
  have hble : Nat.ble v.length (Nat.sub (Nat.succ (L - 1)) t) = true := Nat.ble_eq_true_of_le (by
    change v.length ≤ L - 1 + 1 - t; omega)
  have hhas : hasP (pwr E Z) v = true := hasP_ok (hpw.imp id fun h => hrep.mem.1 h)
  have all : ∀ p ∈ M, topC (lz Z) (mz Z) (pL (Q.map fun _ => 16)) (L - 1) p.1 p.2 (L - 1) t (pL (Q.map fun e => 16 + (L - 1 - e.2)) - sumc v) v = false := by
    intro p hpM
    have h2 := hchk p hpM
    simp only [chk, frc_eq, st_eq] at h2
    have h3 := anySub_false (by simp) h2 v hsub hcov
    simp only [startv, bR, hhas, hble, Bool.cond_true] at h3
    exact child_sound X (f := fun z r => topC (lz Z) (mz Z) _ (L - 1) p.1 p.2 (L - 1) t z r) (fun h => rfl) hst hm (by omega) h3
  refine topC_sound X (RZ_R E Z) (RZ_R2 E Z) hMf all hst hcod (by omega) hl ?_
  intro q hq hs
  rw [RZ_set] at hs
  refine Nat.find_min hex (show q < Nat.find hex by omega) (hs.mono le_rfl ?_)
  rintro x ((hx | hx) | hx)
  · exact Or.inl hx
  · exact Or.inl (hSW hx)
  · exact Or.inr hx
def FF : ℕ := 2 ^ MM - 1
lemma ffull : mFull [(FF, 1)] = true := by decide +kernel
noncomputable def okT (E Q : List (ℕ × ℕ)) (Z L : ℕ) (ts : List ℕ) : Bool := ts.all (fun t => !chk E Q Z (L - 1) t FF 1)
noncomputable def okE (E Q : List (ℕ × ℕ)) (e : ℕ × ℕ) : Bool := pOk e.1 Q && Nat.ble e.2 16 && (Q.any (fun x => Nat.ble e.2 x.2) || okT E Q e.1 e.2 (List.range e.2))
lemma imp_okE {E Q : List (ℕ × ℕ)} {e : ℕ × ℕ} (hE : E = [] ∨ ∃ e' ∈ six, E = [e'] ∧ Imp [] e.1 e.2) (h : okE E Q e = true) (hI : ∀ e' ∈ Q, Imp E e'.1 e'.2) : Imp E e.1 e.2 := by
  simp only [okE, okT, Bool.and_eq_true, Bool.or_eq_true, List.any_eq_true, List.all_eq_true, List.mem_range, Bool.not_eq_true'] at h
  refine imp_of hE h.1.1 (Nat.le_of_ble_eq_true h.1.2) hI (h.2.imp (fun ⟨x, hx, hx2⟩ => ⟨x, hx, Nat.le_of_ble_eq_true hx2⟩) fun h t ht =>
    ⟨[(FF, 1)], ffull, fun p hp => ?_⟩)
  simp only [List.mem_singleton] at hp; subst hp; exact h t ht
def pr (T : List (ℕ × ℕ)) (Z : ℕ) : List (ℕ × ℕ) := T.filter (fun e => Nat.beq (Nat.land Z e.1) Z && !Nat.beq Z e.1)
lemma okAll {T U : List (ℕ × ℕ)} (h : U.all (fun e => okE [] (pr T e.1) e) = true)
    (hT : ∀ e ∈ T, Imp [] e.1 e.2) : ∀ e ∈ U, Imp [] e.1 e.2 := fun e he => imp_okE
  (Or.inl rfl) (List.all_eq_true.1 h e he) (fun e' h' => hT e' (List.mem_of_mem_filter h'))
lemma apI {A B : List (ℕ × ℕ)} (ha : ∀ e ∈ A, Imp [] e.1 e.2) (hb : ∀ e ∈ B, Imp [] e.1 e.2) : ∀ e ∈ A ++ B, Imp [] e.1 e.2 := fun e he =>
  (List.mem_append.1 he).elim (ha e) (hb e)
noncomputable def okS (T : List (ℕ × ℕ)) (Z K : ℕ) (p : ℕ × ℕ × ℕ) : Bool := !chk [] (pr T Z) Z K p.1 p.2.1 p.2.2
def selT (M : List (ℕ × ℕ × ℕ)) (t : ℕ) : List (ℕ × ℕ) := (M.filter (fun p => Nat.beq p.1 t)).map Prod.snd
def okP (T : List (ℕ × ℕ)) (Z L : ℕ) (M : List (ℕ × ℕ × ℕ)) : Bool := pOk Z (pr T Z) && Nat.ble L 16 && (List.range L).all (fun t => mFull (selT M t))
lemma imp_run {T : List (ℕ × ℕ)} {Z L : ℕ} (M : List (ℕ × ℕ × ℕ)) (hT : ∀ e ∈ T, Imp [] e.1 e.2) (hp : okP T Z L M = true) (h : M.all (okS T Z (L - 1)) = true) : Imp [] Z L := by
  simp only [okP, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hp
  refine imp_of (Or.inl rfl) hp.1.1 (Nat.le_of_ble_eq_true hp.1.2) (fun e he => hT e (List.mem_of_mem_filter he)) (Or.inr fun t ht => ⟨selT M t, hp.2 t ht, fun p hq => ?_⟩)
  simp only [selT, List.mem_map, List.mem_filter] at hq
  obtain ⟨q, ⟨hq1, hq2⟩, rfl⟩ := hq
  have h1 := List.all_eq_true.1 h q hq1
  have h2 : q.1 = t := Nat.eq_of_beq_eq_true hq2
  simp only [okS, Bool.not_eq_true'] at h1
  rw [← h2]; exact h1
lemma appS {T : List (ℕ × ℕ)} {Z K : ℕ} {A B : List (ℕ × ℕ × ℕ)} (ha : A.all (okS T Z K) = true) (hb : B.all (okS T Z K) = true) : (A ++ B).all (okS T Z K) = true := by
  rw [List.all_append, ha, hb]; rfl
lemma one1 {Z L : ℕ} (h : Imp [] Z L) : ∀ e ∈ [(Z, L)], Imp [] e.1 e.2 := fun e he => by
  simp only [List.mem_singleton] at he; subst he; exact h
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
section circuit
variable (m : ℕ)
def gv (w : List ℕ) (g : Gate) : ℕ := match g.op, g.inputs with
  | .and, [] => m
  | .and, [i] => w.getD i 0
  | .and, i :: j :: _ => w.getD i 0 &&& w.getD j 0
  | .or, [] => 0
  | .or, [i] => w.getD i 0
  | .or, i :: j :: _ => w.getD i 0 ||| w.getD j 0
  | .not, [] => m
  | .not, i :: _ => w.getD i 0 ^^^ m
  | _, _ => 0
def ex (gs : List Gate) (w : List ℕ) : List ℕ := gs.foldl (fun w g => w ++ [gv m w g]) w
lemma getD_mem {S : Set ℕ} {w : List ℕ} (hw : ∀ x ∈ w, x ∈ S) (h0 : 0 ∈ S) (i : ℕ) : w.getD i 0 ∈ S := by
  rw [List.getD_eq_getElem?_getD]
  by_cases h : i < w.length
  · rw [List.getElem?_eq_getElem h]; exact hw _ (List.getElem_mem h)
  · rw [List.getElem?_eq_none (by omega)]; exact h0
lemma ex_sol {T : ℕ} (gs : List Gate) : ∀ (w : List ℕ) (S : Set ℕ), (∀ x ∈ w, x ∈ S) → 0 ∈ S → m ∈ S →
    (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) →
    (∃ i, (ex m gs w).getD i 0 = T) → Sol Z0 m T gs.length S := by
  induction gs with
  | nil =>
    rintro w S hw h0 _ _ ⟨i, rfl⟩
    exact .done (getD_mem hw h0 i)
  | cons g gs ih =>
    intro w S hw h0 hm hg hT
    have hgs := fun x hx => hg x (List.mem_cons_of_mem _ hx)
    have rd := fun i => getD_mem hw h0 i
    have stay : gv m w g ∈ S → Sol Z0 m T (g :: gs).length S := fun h =>
      (ih (w ++ [gv m w g]) S (fun x hx => by
        simp only [List.mem_append, List.mem_singleton] at hx
        rcases hx with hx | rfl
        · exact hw x hx
        · exact h) h0 hm hgs hT).mono (by simp) subset_rfl
    have go : Sol Z0 m T gs.length (insert (gv m w g) S) := ih (w ++ [gv m w g]) _ (fun x hx => by
        simp only [List.mem_append, List.mem_singleton] at hx
        rcases hx with hx | rfl
        · exact Or.inr (hw x hx)
        · exact Or.inl rfl) (Or.inr h0) (Or.inr hm) hgs hT
    obtain ⟨hop, hlen⟩ := hg g List.mem_cons_self
    obtain ⟨o, l⟩ := g
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
    rcases hop with rfl | rfl | rfl
    · match l with
      | [] => exact stay hm
      | [i] => exact stay (rd i)
      | i :: j :: _ => exact .bi (d := false) (rd i) (rd j) (al0 _ _ _) go
    · match l with
      | [] => exact stay h0
      | [i] => exact stay (rd i)
      | i :: j :: _ => exact .bi (d := true) (rd i) (rd j) (al0 _ _ _) go
    · match l with
      | [] => exact stay hm
      | i :: _ => exact .un (rd i) go
lemma gv_sub {w : List ℕ} (hw : ∀ x ∈ w, x &&& m = x) (g : Gate) : gv m w g &&& m = gv m w g := by
  have rd : ∀ i, w.getD i 0 &&& m = w.getD i 0 := fun i => getD_mem (S := {x | x &&& m = x}) hw (by simp) i
  unfold gv
  split
  · simp
  · exact rd _
  · rw [Nat.and_assoc, rd]
  · simp
  · exact rd _
  · rw [Nat.and_or_distrib_right, rd, rd]
  · simp
  · rw [and_neg (Nat.and_self m), rd]
  · simp
lemma ex_sub {gs : List Gate} : ∀ {w : List ℕ}, (∀ x ∈ w, x &&& m = x) → ∀ x ∈ ex m gs w, x &&& m = x := by
  induction gs with
  | nil => intro w hw; exact hw
  | cons g gs ih =>
    intro w hw
    refine ih (w := w ++ [gv m w g]) fun x hx => ?_
    simp only [List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact hw x hx
    · exact gv_sub m hw g
lemma getD_map (w : List ℕ) (b i : ℕ) : (w.map (fun x => x.testBit b)).getD i false = (w.getD i 0).testBit b := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases w[i]? <;> simp
lemma gv_bit {b : ℕ} (hb : m.testBit b = true) (w : List ℕ) (g : Gate)
    (hg : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    (gv m w g).testBit b = g.op.eval (g.inputs.map fun i => (w.map (fun x => x.testBit b)).getD i false) := by
  have e1 : ∀ l, GateOp.and.eval l = l.all id := fun _ => rfl
  have e2 : ∀ l, GateOp.or.eval l = l.any id := fun _ => rfl
  have e3 : ∀ l, GateOp.not.eval l = !(l.headD false) := fun _ => rfl
  obtain ⟨o, l⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  simp only [getD_map]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  simp only at hlen
  rcases hop with rfl | rfl | rfl
  · match l, hlen with
    | [], _ => simp [gv, e1, hb]
    | [i], _ => simp [gv, e1]
    | [i, j], _ => simp [gv, e1]
  · match l, hlen with
    | [], _ => simp [gv, e2]
    | [i], _ => simp [gv, e2]
    | [i, j], _ => simp [gv, e2]
  · match l, hlen with
    | [], _ => simp [gv, e3, hb]
    | [i], _ => simp [gv, e3, hb]
    | [i, j], _ => simp [gv, e3, hb]
lemma ex_bit {b : ℕ} (hb : m.testBit b = true) (gs : List Gate) : ∀ (w : List ℕ),
    (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) →
    (ex m gs w).map (fun x => x.testBit b) =
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (w.map (fun x => x.testBit b)) := by
  induction gs with
  | nil => intro w _; rfl
  | cons g gs ih =>
    intro w hg
    rw [List.foldl_cons, ← gv_bit m hb w g (hg g List.mem_cons_self)]
    have := ih (w ++ [gv m w g]) (fun x hx => hg x (List.mem_cons_of_mem _ hx))
    rw [List.map_append] at this
    exact this
end circuit
def f (x : Fin 9 → Bool) : Bool := (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 5) || (x 1 && x 6) || (x 3 && x 6) || (x 2 && x 7) || (x 3 && x 7) || (x 5 && x 7) || (x 0 && x 8) || (x 2 && x 8) || (x 4 && x 8) || (x 6 && x 8)
def EF : ℕ := ((((((((((((rawP.getD 0 0 &&& rawP.getD 4 0) ||| (rawP.getD 1 0 &&& rawP.getD 5 0)) ||| (rawP.getD 2 0 &&& rawP.getD 5 0)) ||| (rawP.getD 1 0 &&& rawP.getD 6 0)) ||| (rawP.getD 3 0 &&& rawP.getD 6 0)) ||| (rawP.getD 2 0 &&& rawP.getD 7 0)) ||| (rawP.getD 3 0 &&& rawP.getD 7 0)) ||| (rawP.getD 5 0 &&& rawP.getD 7 0)) ||| (rawP.getD 0 0 &&& rawP.getD 8 0)) ||| (rawP.getD 2 0 &&& rawP.getD 8 0)) ||| (rawP.getD 4 0 &&& rawP.getD 8 0)) ||| (rawP.getD 6 0 &&& rawP.getD 8 0))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma EF_ok : EF &&& mz 0 = tz 0 := by decide +kernel
lemma rawP_len : rawP.length = 9 := rfl
lemma row_list (b : ℕ) : List.ofFn (fun v : Fin 9 => (rawP.getD v.val 0).testBit b) = rawP.map (fun x => x.testBit b) := by
  apply List.ext_getElem
  · simp [rawP_len]
  · intro i h1 h2
    have : i < rawP.length := by simpa using h2
    rw [List.getElem_ofFn, List.getElem_map, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem this]; rfl
lemma f_bit (k : ℕ) : EF.testBit k = f (fun v : Fin 9 => (rawP.getD v.val 0).testBit k) := by
  simp only [f, EF, Nat.testBit_or, Nat.testBit_and]
  rfl
theorem bridge (D : PEqualNP.CircuitLowerBounds.Circuit) (hD : PEqualNP.MetaComplexity.FanInTwo D)
    (hf : ∀ y : Fin 9 → Bool, D.eval (List.ofFn y) = f y) :
    Sol Z0 (mz 0) (tz 0) D.size (C (mz 0) (WZ [] 0)) := by
  obtain ⟨gates, out⟩ := D
  let row : ℕ → Fin 9 → Bool := fun k v => (rawP.getD v.val 0).testBit k
  let init : List ℕ := rawP.map (· &&& mz 0)
  have hinit_sub : ∀ x ∈ init, x &&& mz 0 = x := by
    intro x hx
    simp only [init, List.mem_map] at hx
    obtain ⟨w, _, rfl⟩ := hx
    rw [Nat.and_assoc, Nat.and_self]
  have hinit_mem : ∀ x ∈ init, x ∈ C (mz 0) (WZ [] 0) := by
    intro x hx
    simp only [init, List.mem_map] at hx
    obtain ⟨w, hw, rfl⟩ := hx
    exact Or.inl ⟨w, by simp [rawL, hw], rfl⟩
  have hinit_bits : ∀ k, (mz 0).testBit k = true → init.map (fun x => x.testBit k) = List.ofFn (row k) := by
    intro k hk
    simp only [init, List.map_map, Function.comp_def, Nat.testBit_and, hk, Bool.and_true]
    rw [row_list]
  have hout : (ex (mz 0) gates init).getD out 0 = tz 0 := by
    rw [← EF_ok]
    have hsub : ∀ x ∈ ex (mz 0) gates init, x &&& mz 0 = x := ex_sub (mz 0) hinit_sub
    have hsub' := getD_mem (S := {x | x &&& mz 0 = x}) hsub (by simp) out
    apply Nat.eq_of_testBit_eq; intro k
    have e1 := congrArg (fun x => x.testBit k) hsub'
    simp only [Nat.testBit_and] at e1
    rw [← e1, Nat.testBit_and]
    cases hk : (mz 0).testBit k with
    | false => simp
    | true =>
      simp only [Bool.and_true]
      rw [← getD_map, ex_bit (mz 0) hk gates init hD, hinit_bits k hk]
      have h := hf (row k)
      change (gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
        (List.ofFn (row k))).getD out false = f (row k) at h
      rw [h]
      exact (f_bit k).symm
  exact ex_sol (mz 0) gates init (C (mz 0) (WZ [] 0))
    hinit_mem (Or.inr (Set.mem_insert _ _)) (Or.inr (Set.mem_insert_of_mem _ rfl))
    hD ⟨out, hout⟩


lemma emptyBounds : ∀ e ∈ ([] : List (ℕ × ℕ)), Imp [] e.1 e.2 := by simp
lemma addBound {z b : ℕ} {xs : List (ℕ × ℕ)} (a : Imp [] z b) (h : ∀ e ∈ xs, Imp [] e.1 e.2) : ∀ e ∈ (z,b) :: xs, Imp [] e.1 e.2 := by
  intro e he
  rcases List.mem_cons.mp he with rfl | hx
  · exact a
  · exact h e hx
def co786 : List (ℕ × ℕ) := []
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes786 : okE [] co786 (786, 7) = true := by decide +kernel
lemma lo786 : Imp [] 786 7 := imp_okE (e := (786, 7)) (Or.inl rfl) yes786 emptyBounds
def co788 : List (ℕ × ℕ) := []
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes788 : okE [] co788 (788, 7) = true := by decide +kernel
lemma lo788 : Imp [] 788 7 := imp_okE (e := (788, 7)) (Or.inl rfl) yes788 emptyBounds
def co792 : List (ℕ × ℕ) := []
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes792 : okE [] co792 (792, 7) = true := by decide +kernel
lemma lo792 : Imp [] 792 7 := imp_okE (e := (792, 7)) (Or.inl rfl) yes792 emptyBounds
def co1128 : List (ℕ × ℕ) := []
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes1128 : okE [] co1128 (1128, 7) = true := by decide +kernel
lemma lo1128 : Imp [] 1128 7 := imp_okE (e := (1128, 7)) (Or.inl rfl) yes1128 emptyBounds
def co4290 : List (ℕ × ℕ) := []
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes4290 : okE [] co4290 (4290, 7) = true := by decide +kernel
lemma lo4290 : Imp [] 4290 7 := imp_okE (e := (4290, 7)) (Or.inl rfl) yes4290 emptyBounds
def co8451 : List (ℕ × ℕ) := []
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes8451 : okE [] co8451 (8451, 7) = true := by decide +kernel
lemma lo8451 : Imp [] 8451 7 := imp_okE (e := (8451, 7)) (Or.inl rfl) yes8451 emptyBounds
def co8453 : List (ℕ × ℕ) := []
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes8453 : okE [] co8453 (8453, 7) = true := by decide +kernel
lemma lo8453 : Imp [] 8453 7 := imp_okE (e := (8453, 7)) (Or.inl rfl) yes8453 emptyBounds
def co8457 : List (ℕ × ℕ) := []
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes8457 : okE [] co8457 (8457, 7) = true := by decide +kernel
lemma lo8457 : Imp [] 8457 7 := imp_okE (e := (8457, 7)) (Or.inl rfl) yes8457 emptyBounds
def co16518 : List (ℕ × ℕ) := []
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes16518 : okE [] co16518 (16518, 7) = true := by decide +kernel
lemma lo16518 : Imp [] 16518 7 := imp_okE (e := (16518, 7)) (Or.inl rfl) yes16518 emptyBounds
def co65580 : List (ℕ × ℕ) := []
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes65580 : okE [] co65580 (65580, 7) = true := by decide +kernel
lemma lo65580 : Imp [] 65580 7 := imp_okE (e := (65580, 7)) (Or.inl rfl) yes65580 emptyBounds
def co578 : List (ℕ × ℕ) := []
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes578 : okE [] co578 (578, 7) = true := by decide +kernel
lemma lo578 : Imp [] 578 7 := imp_okE (e := (578, 7)) (Or.inl rfl) yes578 emptyBounds
def co584 : List (ℕ × ℕ) := []
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes584 : okE [] co584 (584, 7) = true := by decide +kernel
lemma lo584 : Imp [] 584 7 := imp_okE (e := (584, 7)) (Or.inl rfl) yes584 emptyBounds
def co592 : List (ℕ × ℕ) := []
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes592 : okE [] co592 (592, 7) = true := by decide +kernel
lemma lo592 : Imp [] 592 7 := imp_okE (e := (592, 7)) (Or.inl rfl) yes592 emptyBounds
def co832 : List (ℕ × ℕ) := []
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes832 : okE [] co832 (832, 7) = true := by decide +kernel
lemma lo832 : Imp [] 832 7 := imp_okE (e := (832, 7)) (Or.inl rfl) yes832 emptyBounds
def co1060 : List (ℕ × ℕ) := []
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes1060 : okE [] co1060 (1060, 7) = true := by decide +kernel
lemma lo1060 : Imp [] 1060 7 := imp_okE (e := (1060, 7)) (Or.inl rfl) yes1060 emptyBounds
def co1092 : List (ℕ × ℕ) := []
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes1092 : okE [] co1092 (1092, 7) = true := by decide +kernel
lemma lo1092 : Imp [] 1092 7 := imp_okE (e := (1092, 7)) (Or.inl rfl) yes1092 emptyBounds
def co1160 : List (ℕ × ℕ) := []
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes1160 : okE [] co1160 (1160, 7) = true := by decide +kernel
lemma lo1160 : Imp [] 1160 7 := imp_okE (e := (1160, 7)) (Or.inl rfl) yes1160 emptyBounds
def co4130 : List (ℕ × ℕ) := []
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes4130 : okE [] co4130 (4130, 7) = true := by decide +kernel
lemma lo4130 : Imp [] 4130 7 := imp_okE (e := (4130, 7)) (Or.inl rfl) yes4130 emptyBounds
def co4164 : List (ℕ × ℕ) := []
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes4164 : okE [] co4164 (4164, 7) = true := by decide +kernel
lemma lo4164 : Imp [] 4164 7 := imp_okE (e := (4164, 7)) (Or.inl rfl) yes4164 emptyBounds
def co4228 : List (ℕ × ℕ) := []
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes4228 : okE [] co4228 (4228, 7) = true := by decide +kernel
lemma lo4228 : Imp [] 4228 7 := imp_okE (e := (4228, 7)) (Or.inl rfl) yes4228 emptyBounds
def co5124 : List (ℕ × ℕ) := []
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes5124 : okE [] co5124 (5124, 7) = true := by decide +kernel
lemma lo5124 : Imp [] 5124 7 := imp_okE (e := (5124, 7)) (Or.inl rfl) yes5124 emptyBounds
def co5152 : List (ℕ × ℕ) := []
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes5152 : okE [] co5152 (5152, 7) = true := by decide +kernel
lemma lo5152 : Imp [] 5152 7 := imp_okE (e := (5152, 7)) (Or.inl rfl) yes5152 emptyBounds
def co5184 : List (ℕ × ℕ) := []
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes5184 : okE [] co5184 (5184, 7) = true := by decide +kernel
lemma lo5184 : Imp [] 5184 7 := imp_okE (e := (5184, 7)) (Or.inl rfl) yes5184 emptyBounds
def co5248 : List (ℕ × ℕ) := []
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes5248 : okE [] co5248 (5248, 7) = true := by decide +kernel
lemma lo5248 : Imp [] 5248 7 := imp_okE (e := (5248, 7)) (Or.inl rfl) yes5248 emptyBounds
def co8257 : List (ℕ × ℕ) := []
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes8257 : okE [] co8257 (8257, 7) = true := by decide +kernel
lemma lo8257 : Imp [] 8257 7 := imp_okE (e := (8257, 7)) (Or.inl rfl) yes8257 emptyBounds
def co8258 : List (ℕ × ℕ) := []
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes8258 : okE [] co8258 (8258, 7) = true := by decide +kernel
lemma lo8258 : Imp [] 8258 7 := imp_okE (e := (8258, 7)) (Or.inl rfl) yes8258 emptyBounds
def co8264 : List (ℕ × ℕ) := []
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes8264 : okE [] co8264 (8264, 7) = true := by decide +kernel
lemma lo8264 : Imp [] 8264 7 := imp_okE (e := (8264, 7)) (Or.inl rfl) yes8264 emptyBounds
def co8512 : List (ℕ × ℕ) := []
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes8512 : okE [] co8512 (8512, 7) = true := by decide +kernel
lemma lo8512 : Imp [] 8512 7 := imp_okE (e := (8512, 7)) (Or.inl rfl) yes8512 emptyBounds
def co16394 : List (ℕ × ℕ) := []
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes16394 : okE [] co16394 (16394, 7) = true := by decide +kernel
lemma lo16394 : Imp [] 16394 7 := imp_okE (e := (16394, 7)) (Or.inl rfl) yes16394 emptyBounds
def co16396 : List (ℕ × ℕ) := []
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes16396 : okE [] co16396 (16396, 7) = true := by decide +kernel
lemma lo16396 : Imp [] 16396 7 := imp_okE (e := (16396, 7)) (Or.inl rfl) yes16396 emptyBounds
def co16456 : List (ℕ × ℕ) := []
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes16456 : okE [] co16456 (16456, 7) = true := by decide +kernel
lemma lo16456 : Imp [] 16456 7 := imp_okE (e := (16456, 7)) (Or.inl rfl) yes16456 emptyBounds
def co16520 : List (ℕ × ℕ) := []
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes16520 : okE [] co16520 (16520, 7) = true := by decide +kernel
lemma lo16520 : Imp [] 16520 7 := imp_okE (e := (16520, 7)) (Or.inl rfl) yes16520 emptyBounds
def co20482 : List (ℕ × ℕ) := []
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes20482 : okE [] co20482 (20482, 7) = true := by decide +kernel
lemma lo20482 : Imp [] 20482 7 := imp_okE (e := (20482, 7)) (Or.inl rfl) yes20482 emptyBounds
def co20484 : List (ℕ × ℕ) := []
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes20484 : okE [] co20484 (20484, 7) = true := by decide +kernel
lemma lo20484 : Imp [] 20484 7 := imp_okE (e := (20484, 7)) (Or.inl rfl) yes20484 emptyBounds
def co20544 : List (ℕ × ℕ) := []
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes20544 : okE [] co20544 (20544, 7) = true := by decide +kernel
lemma lo20544 : Imp [] 20544 7 := imp_okE (e := (20544, 7)) (Or.inl rfl) yes20544 emptyBounds
def co20608 : List (ℕ × ℕ) := []
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes20608 : okE [] co20608 (20608, 7) = true := by decide +kernel
lemma lo20608 : Imp [] 20608 7 := imp_okE (e := (20608, 7)) (Or.inl rfl) yes20608 emptyBounds
def co32778 : List (ℕ × ℕ) := []
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes32778 : okE [] co32778 (32778, 7) = true := by decide +kernel
lemma lo32778 : Imp [] 32778 7 := imp_okE (e := (32778, 7)) (Or.inl rfl) yes32778 emptyBounds
def co32785 : List (ℕ × ℕ) := []
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes32785 : okE [] co32785 (32785, 7) = true := by decide +kernel
lemma lo32785 : Imp [] 32785 7 := imp_okE (e := (32785, 7)) (Or.inl rfl) yes32785 emptyBounds
def co33026 : List (ℕ × ℕ) := []
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes33026 : okE [] co33026 (33026, 7) = true := by decide +kernel
lemma lo33026 : Imp [] 33026 7 := imp_okE (e := (33026, 7)) (Or.inl rfl) yes33026 emptyBounds
def co33032 : List (ℕ × ℕ) := []
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes33032 : okE [] co33032 (33032, 7) = true := by decide +kernel
lemma lo33032 : Imp [] 33032 7 := imp_okE (e := (33032, 7)) (Or.inl rfl) yes33032 emptyBounds
def co33282 : List (ℕ × ℕ) := []
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes33282 : okE [] co33282 (33282, 7) = true := by decide +kernel
lemma lo33282 : Imp [] 33282 7 := imp_okE (e := (33282, 7)) (Or.inl rfl) yes33282 emptyBounds
def co33288 : List (ℕ × ℕ) := []
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes33288 : okE [] co33288 (33288, 7) = true := by decide +kernel
lemma lo33288 : Imp [] 33288 7 := imp_okE (e := (33288, 7)) (Or.inl rfl) yes33288 emptyBounds
def co33296 : List (ℕ × ℕ) := []
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes33296 : okE [] co33296 (33296, 7) = true := by decide +kernel
lemma lo33296 : Imp [] 33296 7 := imp_okE (e := (33296, 7)) (Or.inl rfl) yes33296 emptyBounds
def co33536 : List (ℕ × ℕ) := []
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes33536 : okE [] co33536 (33536, 7) = true := by decide +kernel
lemma lo33536 : Imp [] 33536 7 := imp_okE (e := (33536, 7)) (Or.inl rfl) yes33536 emptyBounds
def co40961 : List (ℕ × ℕ) := []
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes40961 : okE [] co40961 (40961, 7) = true := by decide +kernel
lemma lo40961 : Imp [] 40961 7 := imp_okE (e := (40961, 7)) (Or.inl rfl) yes40961 emptyBounds
def co40962 : List (ℕ × ℕ) := []
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes40962 : okE [] co40962 (40962, 7) = true := by decide +kernel
lemma lo40962 : Imp [] 40962 7 := imp_okE (e := (40962, 7)) (Or.inl rfl) yes40962 emptyBounds
def co40968 : List (ℕ × ℕ) := []
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes40968 : okE [] co40968 (40968, 7) = true := by decide +kernel
lemma lo40968 : Imp [] 40968 7 := imp_okE (e := (40968, 7)) (Or.inl rfl) yes40968 emptyBounds
def co41216 : List (ℕ × ℕ) := []
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes41216 : okE [] co41216 (41216, 7) = true := by decide +kernel
lemma lo41216 : Imp [] 41216 7 := imp_okE (e := (41216, 7)) (Or.inl rfl) yes41216 emptyBounds
def co65542 : List (ℕ × ℕ) := []
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes65542 : okE [] co65542 (65542, 7) = true := by decide +kernel
lemma lo65542 : Imp [] 65542 7 := imp_okE (e := (65542, 7)) (Or.inl rfl) yes65542 emptyBounds
def co65546 : List (ℕ × ℕ) := []
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes65546 : okE [] co65546 (65546, 7) = true := by decide +kernel
lemma lo65546 : Imp [] 65546 7 := imp_okE (e := (65546, 7)) (Or.inl rfl) yes65546 emptyBounds
def co65570 : List (ℕ × ℕ) := []
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes65570 : okE [] co65570 (65570, 7) = true := by decide +kernel
lemma lo65570 : Imp [] 65570 7 := imp_okE (e := (65570, 7)) (Or.inl rfl) yes65570 emptyBounds
def co65602 : List (ℕ × ℕ) := []
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes65602 : okE [] co65602 (65602, 7) = true := by decide +kernel
lemma lo65602 : Imp [] 65602 7 := imp_okE (e := (65602, 7)) (Or.inl rfl) yes65602 emptyBounds
def co66564 : List (ℕ × ℕ) := []
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes66564 : okE [] co66564 (66564, 7) = true := by decide +kernel
lemma lo66564 : Imp [] 66564 7 := imp_okE (e := (66564, 7)) (Or.inl rfl) yes66564 emptyBounds
def co66568 : List (ℕ × ℕ) := []
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes66568 : okE [] co66568 (66568, 7) = true := by decide +kernel
lemma lo66568 : Imp [] 66568 7 := imp_okE (e := (66568, 7)) (Or.inl rfl) yes66568 emptyBounds
def co66592 : List (ℕ × ℕ) := []
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes66592 : okE [] co66592 (66592, 7) = true := by decide +kernel
lemma lo66592 : Imp [] 66592 7 := imp_okE (e := (66592, 7)) (Or.inl rfl) yes66592 emptyBounds
def co66624 : List (ℕ × ℕ) := []
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes66624 : okE [] co66624 (66624, 7) = true := by decide +kernel
lemma lo66624 : Imp [] 66624 7 := imp_okE (e := (66624, 7)) (Or.inl rfl) yes66624 emptyBounds
def co11 : List (ℕ × ℕ) := []
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes11 : okE [] co11 (11, 8) = true := by decide +kernel
lemma lo11 : Imp [] 11 8 := imp_okE (e := (11, 8)) (Or.inl rfl) yes11 emptyBounds
def co21 : List (ℕ × ℕ) := []
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes21 : okE [] co21 (21, 8) = true := by decide +kernel
lemma lo21 : Imp [] 21 8 := imp_okE (e := (21, 8)) (Or.inl rfl) yes21 emptyBounds
def co26 : List (ℕ × ℕ) := []
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes26 : okE [] co26 (26, 8) = true := by decide +kernel
lemma lo26 : Imp [] 26 8 := imp_okE (e := (26, 8)) (Or.inl rfl) yes26 emptyBounds
def co35 : List (ℕ × ℕ) := []
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes35 : okE [] co35 (35, 8) = true := by decide +kernel
lemma lo35 : Imp [] 35 8 := imp_okE (e := (35, 8)) (Or.inl rfl) yes35 emptyBounds
def co38 : List (ℕ × ℕ) := []
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes38 : okE [] co38 (38, 8) = true := by decide +kernel
lemma lo38 : Imp [] 38 8 := imp_okE (e := (38, 8)) (Or.inl rfl) yes38 emptyBounds
def co42 : List (ℕ × ℕ) := []
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes42 : okE [] co42 (42, 8) = true := by decide +kernel
lemma lo42 : Imp [] 42 8 := imp_okE (e := (42, 8)) (Or.inl rfl) yes42 emptyBounds
def co49 : List (ℕ × ℕ) := []
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes49 : okE [] co49 (49, 8) = true := by decide +kernel
lemma lo49 : Imp [] 49 8 := imp_okE (e := (49, 8)) (Or.inl rfl) yes49 emptyBounds
def co50 : List (ℕ × ℕ) := []
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes50 : okE [] co50 (50, 8) = true := by decide +kernel
lemma lo50 : Imp [] 50 8 := imp_okE (e := (50, 8)) (Or.inl rfl) yes50 emptyBounds
def co67 : List (ℕ × ℕ) := []
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes67 : okE [] co67 (67, 8) = true := by decide +kernel
lemma lo67 : Imp [] 67 8 := imp_okE (e := (67, 8)) (Or.inl rfl) yes67 emptyBounds
def co73 : List (ℕ × ℕ) := []
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes73 : okE [] co73 (73, 8) = true := by decide +kernel
lemma lo73 : Imp [] 73 8 := imp_okE (e := (73, 8)) (Or.inl rfl) yes73 emptyBounds
def co81 : List (ℕ × ℕ) := []
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes81 : okE [] co81 (81, 8) = true := by decide +kernel
lemma lo81 : Imp [] 81 8 := imp_okE (e := (81, 8)) (Or.inl rfl) yes81 emptyBounds
def co82 : List (ℕ × ℕ) := []
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes82 : okE [] co82 (82, 8) = true := by decide +kernel
lemma lo82 : Imp [] 82 8 := imp_okE (e := (82, 8)) (Or.inl rfl) yes82 emptyBounds
def co88 : List (ℕ × ℕ) := []
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes88 : okE [] co88 (88, 8) = true := by decide +kernel
lemma lo88 : Imp [] 88 8 := imp_okE (e := (88, 8)) (Or.inl rfl) yes88 emptyBounds
def co98 : List (ℕ × ℕ) := []
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes98 : okE [] co98 (98, 8) = true := by decide +kernel
lemma lo98 : Imp [] 98 8 := imp_okE (e := (98, 8)) (Or.inl rfl) yes98 emptyBounds
def co137 : List (ℕ × ℕ) := []
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes137 : okE [] co137 (137, 8) = true := by decide +kernel
lemma lo137 : Imp [] 137 8 := imp_okE (e := (137, 8)) (Or.inl rfl) yes137 emptyBounds
def co138 : List (ℕ × ℕ) := []
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes138 : okE [] co138 (138, 8) = true := by decide +kernel
lemma lo138 : Imp [] 138 8 := imp_okE (e := (138, 8)) (Or.inl rfl) yes138 emptyBounds
def co140 : List (ℕ × ℕ) := []
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes140 : okE [] co140 (140, 8) = true := by decide +kernel
lemma lo140 : Imp [] 140 8 := imp_okE (e := (140, 8)) (Or.inl rfl) yes140 emptyBounds
def co145 : List (ℕ × ℕ) := []
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes145 : okE [] co145 (145, 8) = true := by decide +kernel
lemma lo145 : Imp [] 145 8 := imp_okE (e := (145, 8)) (Or.inl rfl) yes145 emptyBounds
def co152 : List (ℕ × ℕ) := []
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes152 : okE [] co152 (152, 8) = true := by decide +kernel
lemma lo152 : Imp [] 152 8 := imp_okE (e := (152, 8)) (Or.inl rfl) yes152 emptyBounds
def co162 : List (ℕ × ℕ) := []
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes162 : okE [] co162 (162, 8) = true := by decide +kernel
lemma lo162 : Imp [] 162 8 := imp_okE (e := (162, 8)) (Or.inl rfl) yes162 emptyBounds
def co164 : List (ℕ × ℕ) := []
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes164 : okE [] co164 (164, 8) = true := by decide +kernel
lemma lo164 : Imp [] 164 8 := imp_okE (e := (164, 8)) (Or.inl rfl) yes164 emptyBounds
def co168 : List (ℕ × ℕ) := []
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes168 : okE [] co168 (168, 8) = true := by decide +kernel
lemma lo168 : Imp [] 168 8 := imp_okE (e := (168, 8)) (Or.inl rfl) yes168 emptyBounds
def co200 : List (ℕ × ℕ) := []
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes200 : okE [] co200 (200, 8) = true := by decide +kernel
lemma lo200 : Imp [] 200 8 := imp_okE (e := (200, 8)) (Or.inl rfl) yes200 emptyBounds
def co530 : List (ℕ × ℕ) := [(786, 7)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes530 : okE [] co530 (530, 8) = true := by decide +kernel
lemma lo530 : Imp [] 530 8 := imp_okE (e := (530, 8)) (Or.inl rfl) yes530 (addBound lo786 emptyBounds)
def co532 : List (ℕ × ℕ) := [(788, 7)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes532 : okE [] co532 (532, 8) = true := by decide +kernel
lemma lo532 : Imp [] 532 8 := imp_okE (e := (532, 8)) (Or.inl rfl) yes532 (addBound lo788 emptyBounds)
def co536 : List (ℕ × ℕ) := [(792, 7)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes536 : okE [] co536 (536, 8) = true := by decide +kernel
lemma lo536 : Imp [] 536 8 := imp_okE (e := (536, 8)) (Or.inl rfl) yes536 (addBound lo792 emptyBounds)
def co770 : List (ℕ × ℕ) := [(786, 7)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes770 : okE [] co770 (770, 8) = true := by decide +kernel
lemma lo770 : Imp [] 770 8 := imp_okE (e := (770, 8)) (Or.inl rfl) yes770 (addBound lo786 emptyBounds)
def co772 : List (ℕ × ℕ) := [(788, 7)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes772 : okE [] co772 (772, 8) = true := by decide +kernel
lemma lo772 : Imp [] 772 8 := imp_okE (e := (772, 8)) (Or.inl rfl) yes772 (addBound lo788 emptyBounds)
def co776 : List (ℕ × ℕ) := [(792, 7)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes776 : okE [] co776 (776, 8) = true := by decide +kernel
lemma lo776 : Imp [] 776 8 := imp_okE (e := (776, 8)) (Or.inl rfl) yes776 (addBound lo792 emptyBounds)
def co1064 : List (ℕ × ℕ) := [(1128, 7)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes1064 : okE [] co1064 (1064, 8) = true := by decide +kernel
lemma lo1064 : Imp [] 1064 8 := imp_okE (e := (1064, 8)) (Or.inl rfl) yes1064 (addBound lo1128 emptyBounds)
def co1096 : List (ℕ × ℕ) := [(1128, 7)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes1096 : okE [] co1096 (1096, 8) = true := by decide +kernel
lemma lo1096 : Imp [] 1096 8 := imp_okE (e := (1096, 8)) (Or.inl rfl) yes1096 (addBound lo1128 emptyBounds)
def co1120 : List (ℕ × ℕ) := [(1128, 7)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes1120 : okE [] co1120 (1120, 8) = true := by decide +kernel
lemma lo1120 : Imp [] 1120 8 := imp_okE (e := (1120, 8)) (Or.inl rfl) yes1120 (addBound lo1128 emptyBounds)
def co4162 : List (ℕ × ℕ) := [(4290, 7)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes4162 : okE [] co4162 (4162, 8) = true := by decide +kernel
lemma lo4162 : Imp [] 4162 8 := imp_okE (e := (4162, 8)) (Or.inl rfl) yes4162 (addBound lo4290 emptyBounds)
def co4226 : List (ℕ × ℕ) := [(4290, 7)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes4226 : okE [] co4226 (4226, 8) = true := by decide +kernel
lemma lo4226 : Imp [] 4226 8 := imp_okE (e := (4226, 8)) (Or.inl rfl) yes4226 (addBound lo4290 emptyBounds)
def co4288 : List (ℕ × ℕ) := [(4290, 7)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes4288 : okE [] co4288 (4288, 8) = true := by decide +kernel
lemma lo4288 : Imp [] 4288 8 := imp_okE (e := (4288, 8)) (Or.inl rfl) yes4288 (addBound lo4290 emptyBounds)
def co8195 : List (ℕ × ℕ) := [(8451, 7)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes8195 : okE [] co8195 (8195, 8) = true := by decide +kernel
lemma lo8195 : Imp [] 8195 8 := imp_okE (e := (8195, 8)) (Or.inl rfl) yes8195 (addBound lo8451 emptyBounds)
def co8197 : List (ℕ × ℕ) := [(8453, 7)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes8197 : okE [] co8197 (8197, 8) = true := by decide +kernel
lemma lo8197 : Imp [] 8197 8 := imp_okE (e := (8197, 8)) (Or.inl rfl) yes8197 (addBound lo8453 emptyBounds)
def co8201 : List (ℕ × ℕ) := [(8457, 7)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes8201 : okE [] co8201 (8201, 8) = true := by decide +kernel
lemma lo8201 : Imp [] 8201 8 := imp_okE (e := (8201, 8)) (Or.inl rfl) yes8201 (addBound lo8457 emptyBounds)
def co8450 : List (ℕ × ℕ) := [(8451, 7)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes8450 : okE [] co8450 (8450, 8) = true := by decide +kernel
lemma lo8450 : Imp [] 8450 8 := imp_okE (e := (8450, 8)) (Or.inl rfl) yes8450 (addBound lo8451 emptyBounds)
def co8452 : List (ℕ × ℕ) := [(8453, 7)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes8452 : okE [] co8452 (8452, 8) = true := by decide +kernel
lemma lo8452 : Imp [] 8452 8 := imp_okE (e := (8452, 8)) (Or.inl rfl) yes8452 (addBound lo8453 emptyBounds)
def co8456 : List (ℕ × ℕ) := [(8457, 7)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes8456 : okE [] co8456 (8456, 8) = true := by decide +kernel
lemma lo8456 : Imp [] 8456 8 := imp_okE (e := (8456, 8)) (Or.inl rfl) yes8456 (addBound lo8457 emptyBounds)
def co16390 : List (ℕ × ℕ) := [(16518, 7)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes16390 : okE [] co16390 (16390, 8) = true := by decide +kernel
lemma lo16390 : Imp [] 16390 8 := imp_okE (e := (16390, 8)) (Or.inl rfl) yes16390 (addBound lo16518 emptyBounds)
def co16514 : List (ℕ × ℕ) := [(16518, 7)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes16514 : okE [] co16514 (16514, 8) = true := by decide +kernel
lemma lo16514 : Imp [] 16514 8 := imp_okE (e := (16514, 8)) (Or.inl rfl) yes16514 (addBound lo16518 emptyBounds)
def co16516 : List (ℕ × ℕ) := [(16518, 7)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes16516 : okE [] co16516 (16516, 8) = true := by decide +kernel
lemma lo16516 : Imp [] 16516 8 := imp_okE (e := (16516, 8)) (Or.inl rfl) yes16516 (addBound lo16518 emptyBounds)
def co65548 : List (ℕ × ℕ) := [(65580, 7)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes65548 : okE [] co65548 (65548, 8) = true := by decide +kernel
lemma lo65548 : Imp [] 65548 8 := imp_okE (e := (65548, 8)) (Or.inl rfl) yes65548 (addBound lo65580 emptyBounds)
def co65572 : List (ℕ × ℕ) := [(65580, 7)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes65572 : okE [] co65572 (65572, 8) = true := by decide +kernel
lemma lo65572 : Imp [] 65572 8 := imp_okE (e := (65572, 8)) (Or.inl rfl) yes65572 (addBound lo65580 emptyBounds)
def co65576 : List (ℕ × ℕ) := [(65580, 7)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes65576 : okE [] co65576 (65576, 8) = true := by decide +kernel
lemma lo65576 : Imp [] 65576 8 := imp_okE (e := (65576, 8)) (Or.inl rfl) yes65576 (addBound lo65580 emptyBounds)
def co19 : List (ℕ × ℕ) := []
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes19 : okE [] co19 (19, 9) = true := by decide +kernel
lemma lo19 : Imp [] 19 9 := imp_okE (e := (19, 9)) (Or.inl rfl) yes19 emptyBounds
def co25 : List (ℕ × ℕ) := []
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes25 : okE [] co25 (25, 9) = true := by decide +kernel
lemma lo25 : Imp [] 25 9 := imp_okE (e := (25, 9)) (Or.inl rfl) yes25 emptyBounds
def co273 : List (ℕ × ℕ) := []
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes273 : okE [] co273 (273, 9) = true := by decide +kernel
lemma lo273 : Imp [] 273 9 := imp_okE (e := (273, 9)) (Or.inl rfl) yes273 emptyBounds
def co784 : List (ℕ × ℕ) := [(792, 7), (788, 7), (786, 7)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes784 : okE [] co784 (784, 9) = true := by decide +kernel
lemma lo784 : Imp [] 784 9 := imp_okE (e := (784, 9)) (Or.inl rfl) yes784 (addBound lo792 (addBound lo788 (addBound lo786 emptyBounds)))
def co8449 : List (ℕ × ℕ) := [(8457, 7), (8453, 7), (8451, 7)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes8449 : okE [] co8449 (8449, 9) = true := by decide +kernel
lemma lo8449 : Imp [] 8449 9 := imp_okE (e := (8449, 9)) (Or.inl rfl) yes8449 (addBound lo8457 (addBound lo8453 (addBound lo8451 emptyBounds)))
def co74 : List (ℕ × ℕ) := []
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes74 : okE [] co74 (74, 10) = true := by decide +kernel
lemma lo74 : Imp [] 74 10 := imp_okE (e := (74, 10)) (Or.inl rfl) yes74 emptyBounds
def co544 : List (ℕ × ℕ) := []
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes544 : okE [] co544 (544, 7) = true := by decide +kernel
lemma lo544 : Imp [] 544 7 := imp_okE (e := (544, 7)) (Or.inl rfl) yes544 emptyBounds
def co640 : List (ℕ × ℕ) := []
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes640 : okE [] co640 (640, 7) = true := by decide +kernel
lemma lo640 : Imp [] 640 7 := imp_okE (e := (640, 7)) (Or.inl rfl) yes640 emptyBounds
def co1025 : List (ℕ × ℕ) := []
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes1025 : okE [] co1025 (1025, 7) = true := by decide +kernel
lemma lo1025 : Imp [] 1025 7 := imp_okE (e := (1025, 7)) (Or.inl rfl) yes1025 emptyBounds
def co1040 : List (ℕ × ℕ) := []
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes1040 : okE [] co1040 (1040, 7) = true := by decide +kernel
lemma lo1040 : Imp [] 1040 7 := imp_okE (e := (1040, 7)) (Or.inl rfl) yes1040 emptyBounds
def co4097 : List (ℕ × ℕ) := []
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes4097 : okE [] co4097 (4097, 7) = true := by decide +kernel
lemma lo4097 : Imp [] 4097 7 := imp_okE (e := (4097, 7)) (Or.inl rfl) yes4097 emptyBounds
def co4112 : List (ℕ × ℕ) := []
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes4112 : okE [] co4112 (4112, 7) = true := by decide +kernel
lemma lo4112 : Imp [] 4112 7 := imp_okE (e := (4112, 7)) (Or.inl rfl) yes4112 emptyBounds
def co8224 : List (ℕ × ℕ) := []
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes8224 : okE [] co8224 (8224, 7) = true := by decide +kernel
lemma lo8224 : Imp [] 8224 7 := imp_okE (e := (8224, 7)) (Or.inl rfl) yes8224 emptyBounds
def co8320 : List (ℕ × ℕ) := []
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes8320 : okE [] co8320 (8320, 7) = true := by decide +kernel
lemma lo8320 : Imp [] 8320 7 := imp_okE (e := (8320, 7)) (Or.inl rfl) yes8320 emptyBounds
def co16385 : List (ℕ × ℕ) := []
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes16385 : okE [] co16385 (16385, 7) = true := by decide +kernel
lemma lo16385 : Imp [] 16385 7 := imp_okE (e := (16385, 7)) (Or.inl rfl) yes16385 emptyBounds
def co16400 : List (ℕ × ℕ) := []
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes16400 : okE [] co16400 (16400, 7) = true := by decide +kernel
lemma lo16400 : Imp [] 16400 7 := imp_okE (e := (16400, 7)) (Or.inl rfl) yes16400 emptyBounds
def co65537 : List (ℕ × ℕ) := []
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes65537 : okE [] co65537 (65537, 7) = true := by decide +kernel
lemma lo65537 : Imp [] 65537 7 := imp_okE (e := (65537, 7)) (Or.inl rfl) yes65537 emptyBounds
def co65552 : List (ℕ × ℕ) := []
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes65552 : okE [] co65552 (65552, 7) = true := by decide +kernel
lemma lo65552 : Imp [] 65552 7 := imp_okE (e := (65552, 7)) (Or.inl rfl) yes65552 emptyBounds
def co131073 : List (ℕ × ℕ) := []
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes131073 : okE [] co131073 (131073, 7) = true := by decide +kernel
lemma lo131073 : Imp [] 131073 7 := imp_okE (e := (131073, 7)) (Or.inl rfl) yes131073 emptyBounds
def co131076 : List (ℕ × ℕ) := []
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes131076 : okE [] co131076 (131076, 7) = true := by decide +kernel
lemma lo131076 : Imp [] 131076 7 := imp_okE (e := (131076, 7)) (Or.inl rfl) yes131076 emptyBounds
def co131088 : List (ℕ × ℕ) := []
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes131088 : okE [] co131088 (131088, 7) = true := by decide +kernel
lemma lo131088 : Imp [] 131088 7 := imp_okE (e := (131088, 7)) (Or.inl rfl) yes131088 emptyBounds
def co131136 : List (ℕ × ℕ) := []
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes131136 : okE [] co131136 (131136, 7) = true := by decide +kernel
lemma lo131136 : Imp [] 131136 7 := imp_okE (e := (131136, 7)) (Or.inl rfl) yes131136 emptyBounds
def co320 : List (ℕ × ℕ) := [(8512, 7), (832, 7)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes320 : okE [] co320 (320, 8) = true := by decide +kernel
lemma lo320 : Imp [] 320 8 := imp_okE (e := (320, 8)) (Or.inl rfl) yes320 (addBound lo8512 (addBound lo832 emptyBounds))
def co576 : List (ℕ × ℕ) := [(832, 7), (592, 7), (584, 7), (578, 7)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes576 : okE [] co576 (576, 8) = true := by decide +kernel
lemma lo576 : Imp [] 576 8 := imp_okE (e := (576, 8)) (Or.inl rfl) yes576 (addBound lo832 (addBound lo592 (addBound lo584 (addBound lo578 emptyBounds))))
def co1028 : List (ℕ × ℕ) := [(66564, 7), (5124, 7), (1092, 7), (1060, 7)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes1028 : okE [] co1028 (1028, 8) = true := by decide +kernel
lemma lo1028 : Imp [] 1028 8 := imp_okE (e := (1028, 8)) (Or.inl rfl) yes1028 (addBound lo66564 (addBound lo5124 (addBound lo1092 (addBound lo1060 emptyBounds))))
def co4100 : List (ℕ × ℕ) := [(20484, 7), (5124, 7), (4228, 7), (4164, 7)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes4100 : okE [] co4100 (4100, 8) = true := by decide +kernel
lemma lo4100 : Imp [] 4100 8 := imp_okE (e := (4100, 8)) (Or.inl rfl) yes4100 (addBound lo20484 (addBound lo5124 (addBound lo4228 (addBound lo4164 emptyBounds))))
def co5120 : List (ℕ × ℕ) := [(5248, 7), (5184, 7), (5152, 7), (5124, 7)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes5120 : okE [] co5120 (5120, 8) = true := by decide +kernel
lemma lo5120 : Imp [] 5120 8 := imp_okE (e := (5120, 8)) (Or.inl rfl) yes5120 (addBound lo5248 (addBound lo5184 (addBound lo5152 (addBound lo5124 emptyBounds))))
def co8256 : List (ℕ × ℕ) := [(8512, 7), (8264, 7), (8258, 7), (8257, 7)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes8256 : okE [] co8256 (8256, 8) = true := by decide +kernel
lemma lo8256 : Imp [] 8256 8 := imp_okE (e := (8256, 8)) (Or.inl rfl) yes8256 (addBound lo8512 (addBound lo8264 (addBound lo8258 (addBound lo8257 emptyBounds))))
def co16392 : List (ℕ × ℕ) := [(16520, 7), (16456, 7), (16396, 7), (16394, 7)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes16392 : okE [] co16392 (16392, 8) = true := by decide +kernel
lemma lo16392 : Imp [] 16392 8 := imp_okE (e := (16392, 8)) (Or.inl rfl) yes16392 (addBound lo16520 (addBound lo16456 (addBound lo16396 (addBound lo16394 emptyBounds))))
def co20480 : List (ℕ × ℕ) := [(20608, 7), (20544, 7), (20484, 7), (20482, 7)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes20480 : okE [] co20480 (20480, 8) = true := by decide +kernel
lemma lo20480 : Imp [] 20480 8 := imp_okE (e := (20480, 8)) (Or.inl rfl) yes20480 (addBound lo20608 (addBound lo20544 (addBound lo20484 (addBound lo20482 emptyBounds))))
def co32770 : List (ℕ × ℕ) := [(40962, 7), (33282, 7), (33026, 7), (32778, 7)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes32770 : okE [] co32770 (32770, 8) = true := by decide +kernel
lemma lo32770 : Imp [] 32770 8 := imp_okE (e := (32770, 8)) (Or.inl rfl) yes32770 (addBound lo40962 (addBound lo33282 (addBound lo33026 (addBound lo32778 emptyBounds))))
def co32776 : List (ℕ × ℕ) := [(40968, 7), (33288, 7), (33032, 7), (32778, 7)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes32776 : okE [] co32776 (32776, 8) = true := by decide +kernel
lemma lo32776 : Imp [] 32776 8 := imp_okE (e := (32776, 8)) (Or.inl rfl) yes32776 (addBound lo40968 (addBound lo33288 (addBound lo33032 (addBound lo32778 emptyBounds))))
def co33024 : List (ℕ × ℕ) := [(41216, 7), (33536, 7), (33032, 7), (33026, 7)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes33024 : okE [] co33024 (33024, 8) = true := by decide +kernel
lemma lo33024 : Imp [] 33024 8 := imp_okE (e := (33024, 8)) (Or.inl rfl) yes33024 (addBound lo41216 (addBound lo33536 (addBound lo33032 (addBound lo33026 emptyBounds))))
def co33280 : List (ℕ × ℕ) := [(33536, 7), (33296, 7), (33288, 7), (33282, 7)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes33280 : okE [] co33280 (33280, 8) = true := by decide +kernel
lemma lo33280 : Imp [] 33280 8 := imp_okE (e := (33280, 8)) (Or.inl rfl) yes33280 (addBound lo33536 (addBound lo33296 (addBound lo33288 (addBound lo33282 emptyBounds))))
def co40960 : List (ℕ × ℕ) := [(41216, 7), (40968, 7), (40962, 7), (40961, 7)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes40960 : okE [] co40960 (40960, 8) = true := by decide +kernel
lemma lo40960 : Imp [] 40960 8 := imp_okE (e := (40960, 8)) (Or.inl rfl) yes40960 (addBound lo41216 (addBound lo40968 (addBound lo40962 (addBound lo40961 emptyBounds))))
def co65538 : List (ℕ × ℕ) := [(65602, 7), (65570, 7), (65546, 7), (65542, 7)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes65538 : okE [] co65538 (65538, 8) = true := by decide +kernel
lemma lo65538 : Imp [] 65538 8 := imp_okE (e := (65538, 8)) (Or.inl rfl) yes65538 (addBound lo65602 (addBound lo65570 (addBound lo65546 (addBound lo65542 emptyBounds))))
def co66560 : List (ℕ × ℕ) := [(66624, 7), (66592, 7), (66568, 7), (66564, 7)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes66560 : okE [] co66560 (66560, 8) = true := by decide +kernel
lemma lo66560 : Imp [] 66560 8 := imp_okE (e := (66560, 8)) (Or.inl rfl) yes66560 (addBound lo66624 (addBound lo66592 (addBound lo66568 (addBound lo66564 emptyBounds))))
def co33 : List (ℕ × ℕ) := [(49, 8), (35, 8)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes33 : okE [] co33 (33, 9) = true := by decide +kernel
lemma lo33 : Imp [] 33 9 := imp_okE (e := (33, 9)) (Or.inl rfl) yes33 (addBound lo49 (addBound lo35 emptyBounds))
def co48 : List (ℕ × ℕ) := [(50, 8), (49, 8)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes48 : okE [] co48 (48, 9) = true := by decide +kernel
lemma lo48 : Imp [] 48 9 := imp_okE (e := (48, 9)) (Or.inl rfl) yes48 (addBound lo50 (addBound lo49 emptyBounds))
def co65 : List (ℕ × ℕ) := [(81, 8), (73, 8), (67, 8), (8257, 7)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes65 : okE [] co65 (65, 9) = true := by decide +kernel
lemma lo65 : Imp [] 65 9 := imp_okE (e := (65, 9)) (Or.inl rfl) yes65 (addBound lo81 (addBound lo73 (addBound lo67 (addBound lo8257 emptyBounds))))
def co68 : List (ℕ × ℕ) := [(4164, 7), (1092, 7)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes68 : okE [] co68 (68, 9) = true := by decide +kernel
lemma lo68 : Imp [] 68 9 := imp_okE (e := (68, 9)) (Or.inl rfl) yes68 (addBound lo4164 (addBound lo1092 emptyBounds))
def co80 : List (ℕ × ℕ) := [(88, 8), (82, 8), (81, 8), (592, 7)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes80 : okE [] co80 (80, 9) = true := by decide +kernel
lemma lo80 : Imp [] 80 9 := imp_okE (e := (80, 9)) (Or.inl rfl) yes80 (addBound lo88 (addBound lo82 (addBound lo81 (addBound lo592 emptyBounds))))
def co129 : List (ℕ × ℕ) := [(145, 8), (137, 8)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes129 : okE [] co129 (129, 9) = true := by decide +kernel
lemma lo129 : Imp [] 129 9 := imp_okE (e := (129, 9)) (Or.inl rfl) yes129 (addBound lo145 (addBound lo137 emptyBounds))
def co144 : List (ℕ × ℕ) := [(152, 8), (145, 8)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes144 : okE [] co144 (144, 9) = true := by decide +kernel
lemma lo144 : Imp [] 144 9 := imp_okE (e := (144, 9)) (Or.inl rfl) yes144 (addBound lo152 (addBound lo145 emptyBounds))
def co160 : List (ℕ × ℕ) := [(168, 8), (164, 8), (162, 8)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes160 : okE [] co160 (160, 9) = true := by decide +kernel
lemma lo160 : Imp [] 160 9 := imp_okE (e := (160, 9)) (Or.inl rfl) yes160 (addBound lo168 (addBound lo164 (addBound lo162 emptyBounds)))
def co258 : List (ℕ × ℕ) := [(8450, 8), (770, 8), (33026, 7), (8451, 7), (786, 7)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes258 : okE [] co258 (258, 9) = true := by decide +kernel
lemma lo258 : Imp [] 258 9 := imp_okE (e := (258, 9)) (Or.inl rfl) yes258 (addBound lo8450 (addBound lo770 (addBound lo33026 (addBound lo8451 (addBound lo786 emptyBounds)))))
def co260 : List (ℕ × ℕ) := [(8452, 8), (772, 8), (8453, 7), (788, 7)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes260 : okE [] co260 (260, 9) = true := by decide +kernel
lemma lo260 : Imp [] 260 9 := imp_okE (e := (260, 9)) (Or.inl rfl) yes260 (addBound lo8452 (addBound lo772 (addBound lo8453 (addBound lo788 emptyBounds))))
def co264 : List (ℕ × ℕ) := [(8456, 8), (776, 8), (33032, 7), (8457, 7), (792, 7)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes264 : okE [] co264 (264, 9) = true := by decide +kernel
lemma lo264 : Imp [] 264 9 := imp_okE (e := (264, 9)) (Or.inl rfl) yes264 (addBound lo8456 (addBound lo776 (addBound lo33032 (addBound lo8457 (addBound lo792 emptyBounds)))))
def co514 : List (ℕ × ℕ) := [(770, 8), (530, 8), (33282, 7), (578, 7), (786, 7)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes514 : okE [] co514 (514, 9) = true := by decide +kernel
lemma lo514 : Imp [] 514 9 := imp_okE (e := (514, 9)) (Or.inl rfl) yes514 (addBound lo770 (addBound lo530 (addBound lo33282 (addBound lo578 (addBound lo786 emptyBounds)))))
def co516 : List (ℕ × ℕ) := [(772, 8), (532, 8), (788, 7)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes516 : okE [] co516 (516, 9) = true := by decide +kernel
lemma lo516 : Imp [] 516 9 := imp_okE (e := (516, 9)) (Or.inl rfl) yes516 (addBound lo772 (addBound lo532 (addBound lo788 emptyBounds)))
def co520 : List (ℕ × ℕ) := [(776, 8), (536, 8), (33288, 7), (584, 7), (792, 7)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes520 : okE [] co520 (520, 9) = true := by decide +kernel
lemma lo520 : Imp [] 520 9 := imp_okE (e := (520, 9)) (Or.inl rfl) yes520 (addBound lo776 (addBound lo536 (addBound lo33288 (addBound lo584 (addBound lo792 emptyBounds)))))
def co1032 : List (ℕ × ℕ) := [(1096, 8), (1064, 8), (66568, 7), (1160, 7), (1128, 7)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes1032 : okE [] co1032 (1032, 9) = true := by decide +kernel
lemma lo1032 : Imp [] 1032 9 := imp_okE (e := (1032, 9)) (Or.inl rfl) yes1032 (addBound lo1096 (addBound lo1064 (addBound lo66568 (addBound lo1160 (addBound lo1128 emptyBounds)))))
def co1056 : List (ℕ × ℕ) := [(1120, 8), (1064, 8), (66592, 7), (5152, 7), (1060, 7), (1128, 7)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes1056 : okE [] co1056 (1056, 9) = true := by decide +kernel
lemma lo1056 : Imp [] 1056 9 := imp_okE (e := (1056, 9)) (Or.inl rfl) yes1056 (addBound lo1120 (addBound lo1064 (addBound lo66592 (addBound lo5152 (addBound lo1060 (addBound lo1128 emptyBounds))))))
def co1088 : List (ℕ × ℕ) := [(1120, 8), (1096, 8), (66624, 7), (5184, 7), (1092, 7), (1128, 7)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes1088 : okE [] co1088 (1088, 9) = true := by decide +kernel
lemma lo1088 : Imp [] 1088 9 := imp_okE (e := (1088, 9)) (Or.inl rfl) yes1088 (addBound lo1120 (addBound lo1096 (addBound lo66624 (addBound lo5184 (addBound lo1092 (addBound lo1128 emptyBounds))))))
def co4098 : List (ℕ × ℕ) := [(4226, 8), (4162, 8), (20482, 7), (4130, 7), (4290, 7)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes4098 : okE [] co4098 (4098, 9) = true := by decide +kernel
lemma lo4098 : Imp [] 4098 9 := imp_okE (e := (4098, 9)) (Or.inl rfl) yes4098 (addBound lo4226 (addBound lo4162 (addBound lo20482 (addBound lo4130 (addBound lo4290 emptyBounds)))))
def co4160 : List (ℕ × ℕ) := [(4288, 8), (4162, 8), (20544, 7), (5184, 7), (4164, 7), (4290, 7)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes4160 : okE [] co4160 (4160, 9) = true := by decide +kernel
lemma lo4160 : Imp [] 4160 9 := imp_okE (e := (4160, 9)) (Or.inl rfl) yes4160 (addBound lo4288 (addBound lo4162 (addBound lo20544 (addBound lo5184 (addBound lo4164 (addBound lo4290 emptyBounds))))))
def co4224 : List (ℕ × ℕ) := [(4288, 8), (4226, 8), (20608, 7), (5248, 7), (4228, 7), (4290, 7)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes4224 : okE [] co4224 (4224, 9) = true := by decide +kernel
lemma lo4224 : Imp [] 4224 9 := imp_okE (e := (4224, 9)) (Or.inl rfl) yes4224 (addBound lo4288 (addBound lo4226 (addBound lo20608 (addBound lo5248 (addBound lo4228 (addBound lo4290 emptyBounds))))))
def co8194 : List (ℕ × ℕ) := [(8450, 8), (8195, 8), (40962, 7), (8258, 7), (8451, 7)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes8194 : okE [] co8194 (8194, 9) = true := by decide +kernel
lemma lo8194 : Imp [] 8194 9 := imp_okE (e := (8194, 9)) (Or.inl rfl) yes8194 (addBound lo8450 (addBound lo8195 (addBound lo40962 (addBound lo8258 (addBound lo8451 emptyBounds)))))
def co8196 : List (ℕ × ℕ) := [(8452, 8), (8197, 8), (8453, 7)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes8196 : okE [] co8196 (8196, 9) = true := by decide +kernel
lemma lo8196 : Imp [] 8196 9 := imp_okE (e := (8196, 9)) (Or.inl rfl) yes8196 (addBound lo8452 (addBound lo8197 (addBound lo8453 emptyBounds)))
def co8200 : List (ℕ × ℕ) := [(8456, 8), (8201, 8), (40968, 7), (8264, 7), (8457, 7)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes8200 : okE [] co8200 (8200, 9) = true := by decide +kernel
lemma lo8200 : Imp [] 8200 9 := imp_okE (e := (8200, 9)) (Or.inl rfl) yes8200 (addBound lo8456 (addBound lo8201 (addBound lo40968 (addBound lo8264 (addBound lo8457 emptyBounds)))))
def co16386 : List (ℕ × ℕ) := [(16514, 8), (16390, 8), (20482, 7), (16394, 7), (16518, 7)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes16386 : okE [] co16386 (16386, 9) = true := by decide +kernel
lemma lo16386 : Imp [] 16386 9 := imp_okE (e := (16386, 9)) (Or.inl rfl) yes16386 (addBound lo16514 (addBound lo16390 (addBound lo20482 (addBound lo16394 (addBound lo16518 emptyBounds)))))
def co16388 : List (ℕ × ℕ) := [(16516, 8), (16390, 8), (20484, 7), (16396, 7), (16518, 7)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes16388 : okE [] co16388 (16388, 9) = true := by decide +kernel
lemma lo16388 : Imp [] 16388 9 := imp_okE (e := (16388, 9)) (Or.inl rfl) yes16388 (addBound lo16516 (addBound lo16390 (addBound lo20484 (addBound lo16396 (addBound lo16518 emptyBounds)))))
def co16512 : List (ℕ × ℕ) := [(16516, 8), (16514, 8), (20608, 7), (16520, 7), (16518, 7)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes16512 : okE [] co16512 (16512, 9) = true := by decide +kernel
lemma lo16512 : Imp [] 16512 9 := imp_okE (e := (16512, 9)) (Or.inl rfl) yes16512 (addBound lo16516 (addBound lo16514 (addBound lo20608 (addBound lo16520 (addBound lo16518 emptyBounds)))))
def co65540 : List (ℕ × ℕ) := [(65572, 8), (65548, 8), (66564, 7), (65542, 7), (65580, 7)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes65540 : okE [] co65540 (65540, 9) = true := by decide +kernel
lemma lo65540 : Imp [] 65540 9 := imp_okE (e := (65540, 9)) (Or.inl rfl) yes65540 (addBound lo65572 (addBound lo65548 (addBound lo66564 (addBound lo65542 (addBound lo65580 emptyBounds)))))
def co65544 : List (ℕ × ℕ) := [(65576, 8), (65548, 8), (66568, 7), (65546, 7), (65580, 7)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes65544 : okE [] co65544 (65544, 9) = true := by decide +kernel
lemma lo65544 : Imp [] 65544 9 := imp_okE (e := (65544, 9)) (Or.inl rfl) yes65544 (addBound lo65576 (addBound lo65548 (addBound lo66568 (addBound lo65546 (addBound lo65580 emptyBounds)))))
def co65568 : List (ℕ × ℕ) := [(65576, 8), (65572, 8), (66592, 7), (65570, 7), (65580, 7)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes65568 : okE [] co65568 (65568, 9) = true := by decide +kernel
lemma lo65568 : Imp [] 65568 9 := imp_okE (e := (65568, 9)) (Or.inl rfl) yes65568 (addBound lo65576 (addBound lo65572 (addBound lo66592 (addBound lo65570 (addBound lo65580 emptyBounds)))))
def co5 : List (ℕ × ℕ) := [(8197, 8), (21, 8), (8453, 7)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes5 : okE [] co5 (5, 10) = true := by decide +kernel
lemma lo5 : Imp [] 5 10 := imp_okE (e := (5, 10)) (Or.inl rfl) yes5 (addBound lo8197 (addBound lo21 (addBound lo8453 emptyBounds)))
def co6 : List (ℕ × ℕ) := [(16390, 8), (38, 8), (65542, 7), (16518, 7)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes6 : okE [] co6 (6, 10) = true := by decide +kernel
lemma lo6 : Imp [] 6 10 := imp_okE (e := (6, 10)) (Or.inl rfl) yes6 (addBound lo16390 (addBound lo38 (addBound lo65542 (addBound lo16518 emptyBounds))))
def co12 : List (ℕ × ℕ) := [(65548, 8), (140, 8), (16396, 7), (65580, 7)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes12 : okE [] co12 (12, 10) = true := by decide +kernel
lemma lo12 : Imp [] 12 10 := imp_okE (e := (12, 10)) (Or.inl rfl) yes12 (addBound lo65548 (addBound lo140 (addBound lo16396 (addBound lo65580 emptyBounds))))
def co20 : List (ℕ × ℕ) := [(532, 8), (21, 8), (788, 7)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes20 : okE [] co20 (20, 10) = true := by decide +kernel
lemma lo20 : Imp [] 20 10 := imp_okE (e := (20, 10)) (Or.inl rfl) yes20 (addBound lo532 (addBound lo21 (addBound lo788 emptyBounds)))
def co36 : List (ℕ × ℕ) := [(65572, 8), (164, 8), (38, 8), (1060, 7), (65580, 7)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes36 : okE [] co36 (36, 10) = true := by decide +kernel
lemma lo36 : Imp [] 36 10 := imp_okE (e := (36, 10)) (Or.inl rfl) yes36 (addBound lo65572 (addBound lo164 (addBound lo38 (addBound lo1060 (addBound lo65580 emptyBounds)))))
def co40 : List (ℕ × ℕ) := [(65576, 8), (1064, 8), (168, 8), (42, 8), (65580, 7), (1128, 7)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes40 : okE [] co40 (40, 10) = true := by decide +kernel
lemma lo40 : Imp [] 40 10 := imp_okE (e := (40, 10)) (Or.inl rfl) yes40 (addBound lo65576 (addBound lo1064 (addBound lo168 (addBound lo42 (addBound lo65580 (addBound lo1128 emptyBounds))))))
def co130 : List (ℕ × ℕ) := [(16514, 8), (4226, 8), (162, 8), (138, 8), (16518, 7), (4290, 7)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes130 : okE [] co130 (130, 10) = true := by decide +kernel
lemma lo130 : Imp [] 130 10 := imp_okE (e := (130, 10)) (Or.inl rfl) yes130 (addBound lo16514 (addBound lo4226 (addBound lo162 (addBound lo138 (addBound lo16518 (addBound lo4290 emptyBounds))))))
def co132 : List (ℕ × ℕ) := [(16516, 8), (164, 8), (140, 8), (4228, 7), (16518, 7)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes132 : okE [] co132 (132, 10) = true := by decide +kernel
lemma lo132 : Imp [] 132 10 := imp_okE (e := (132, 10)) (Or.inl rfl) yes132 (addBound lo16516 (addBound lo164 (addBound lo140 (addBound lo4228 (addBound lo16518 emptyBounds)))))
def co528 : List (ℕ × ℕ) := [(784, 9), (536, 8), (532, 8), (530, 8), (33296, 7), (592, 7), (792, 7), (788, 7), (786, 7)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes528 : okE [] co528 (528, 10) = true := by decide +kernel
lemma lo528 : Imp [] 528 10 := imp_okE (e := (528, 10)) (Or.inl rfl) yes528 (addBound lo784 (addBound lo536 (addBound lo532 (addBound lo530 (addBound lo33296 (addBound lo592 (addBound lo792 (addBound lo788 (addBound lo786 emptyBounds)))))))))
def co768 : List (ℕ × ℕ) := [(784, 9), (776, 8), (772, 8), (770, 8), (33536, 7), (832, 7), (792, 7), (788, 7), (786, 7)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes768 : okE [] co768 (768, 10) = true := by decide +kernel
lemma lo768 : Imp [] 768 10 := imp_okE (e := (768, 10)) (Or.inl rfl) yes768 (addBound lo784 (addBound lo776 (addBound lo772 (addBound lo770 (addBound lo33536 (addBound lo832 (addBound lo792 (addBound lo788 (addBound lo786 emptyBounds)))))))))
def co8193 : List (ℕ × ℕ) := [(8449, 9), (8201, 8), (8197, 8), (8195, 8), (40961, 7), (8257, 7), (8457, 7), (8453, 7), (8451, 7)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes8193 : okE [] co8193 (8193, 10) = true := by decide +kernel
lemma lo8193 : Imp [] 8193 10 := imp_okE (e := (8193, 10)) (Or.inl rfl) yes8193 (addBound lo8449 (addBound lo8201 (addBound lo8197 (addBound lo8195 (addBound lo40961 (addBound lo8257 (addBound lo8457 (addBound lo8453 (addBound lo8451 emptyBounds)))))))))
def co8448 : List (ℕ × ℕ) := [(8449, 9), (8456, 8), (8452, 8), (8450, 8), (41216, 7), (8512, 7), (8457, 7), (8453, 7), (8451, 7)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes8448 : okE [] co8448 (8448, 10) = true := by decide +kernel
lemma lo8448 : Imp [] 8448 10 := imp_okE (e := (8448, 10)) (Or.inl rfl) yes8448 (addBound lo8449 (addBound lo8456 (addBound lo8452 (addBound lo8450 (addBound lo41216 (addBound lo8512 (addBound lo8457 (addBound lo8453 (addBound lo8451 emptyBounds)))))))))
def co3 : List (ℕ × ℕ) := [(19, 9), (8195, 8), (67, 8), (35, 8), (11, 8), (8451, 7)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes3 : okE [] co3 (3, 11) = true := by decide +kernel
lemma lo3 : Imp [] 3 11 := imp_okE (e := (3, 11)) (Or.inl rfl) yes3 (addBound lo19 (addBound lo8195 (addBound lo67 (addBound lo35 (addBound lo11 (addBound lo8451 emptyBounds))))))
def co9 : List (ℕ × ℕ) := [(25, 9), (8201, 8), (137, 8), (73, 8), (11, 8), (8457, 7)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes9 : okE [] co9 (9, 11) = true := by decide +kernel
lemma lo9 : Imp [] 9 11 := imp_okE (e := (9, 11)) (Or.inl rfl) yes9 (addBound lo25 (addBound lo8201 (addBound lo137 (addBound lo73 (addBound lo11 (addBound lo8457 emptyBounds))))))
def co10 : List (ℕ × ℕ) := [(74, 10), (138, 8), (42, 8), (26, 8), (11, 8), (65546, 7), (32778, 7), (16394, 7)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes10 : okE [] co10 (10, 11) = true := by decide +kernel
lemma lo10 : Imp [] 10 11 := imp_okE (e := (10, 11)) (Or.inl rfl) yes10 (addBound lo74 (addBound lo138 (addBound lo42 (addBound lo26 (addBound lo11 (addBound lo65546 (addBound lo32778 (addBound lo16394 emptyBounds))))))))
def co18 : List (ℕ × ℕ) := [(19, 9), (530, 8), (82, 8), (50, 8), (26, 8), (786, 7)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes18 : okE [] co18 (18, 11) = true := by decide +kernel
lemma lo18 : Imp [] 18 11 := imp_okE (e := (18, 11)) (Or.inl rfl) yes18 (addBound lo19 (addBound lo530 (addBound lo82 (addBound lo50 (addBound lo26 (addBound lo786 emptyBounds))))))
def co24 : List (ℕ × ℕ) := [(25, 9), (536, 8), (152, 8), (88, 8), (26, 8), (792, 7)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes24 : okE [] co24 (24, 11) = true := by decide +kernel
lemma lo24 : Imp [] 24 11 := imp_okE (e := (24, 11)) (Or.inl rfl) yes24 (addBound lo25 (addBound lo536 (addBound lo152 (addBound lo88 (addBound lo26 (addBound lo792 emptyBounds))))))
def co34 : List (ℕ × ℕ) := [(162, 8), (98, 8), (50, 8), (42, 8), (38, 8), (35, 8), (65570, 7), (4130, 7)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes34 : okE [] co34 (34, 11) = true := by decide +kernel
lemma lo34 : Imp [] 34 11 := imp_okE (e := (34, 11)) (Or.inl rfl) yes34 (addBound lo162 (addBound lo98 (addBound lo50 (addBound lo42 (addBound lo38 (addBound lo35 (addBound lo65570 (addBound lo4130 emptyBounds))))))))
def co66 : List (ℕ × ℕ) := [(74, 10), (4162, 8), (98, 8), (82, 8), (67, 8), (65602, 7), (8258, 7), (578, 7), (4290, 7)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes66 : okE [] co66 (66, 11) = true := by decide +kernel
lemma lo66 : Imp [] 66 11 := imp_okE (e := (66, 11)) (Or.inl rfl) yes66 (addBound lo74 (addBound lo4162 (addBound lo98 (addBound lo82 (addBound lo67 (addBound lo65602 (addBound lo8258 (addBound lo578 (addBound lo4290 emptyBounds)))))))))
def co72 : List (ℕ × ℕ) := [(74, 10), (1096, 8), (200, 8), (88, 8), (73, 8), (16456, 7), (8264, 7), (584, 7), (1128, 7)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes72 : okE [] co72 (72, 11) = true := by decide +kernel
lemma lo72 : Imp [] 72 11 := imp_okE (e := (72, 11)) (Or.inl rfl) yes72 (addBound lo74 (addBound lo1096 (addBound lo200 (addBound lo88 (addBound lo73 (addBound lo16456 (addBound lo8264 (addBound lo584 (addBound lo1128 emptyBounds)))))))))
def co136 : List (ℕ × ℕ) := [(200, 8), (168, 8), (152, 8), (140, 8), (138, 8), (137, 8), (16520, 7), (1160, 7)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes136 : okE [] co136 (136, 11) = true := by decide +kernel
lemma lo136 : Imp [] 136 11 := imp_okE (e := (136, 11)) (Or.inl rfl) yes136 (addBound lo200 (addBound lo168 (addBound lo152 (addBound lo140 (addBound lo138 (addBound lo137 (addBound lo16520 (addBound lo1160 emptyBounds))))))))
def co17 : List (ℕ × ℕ) := [(273, 9), (25, 9), (19, 9), (145, 8), (81, 8), (49, 8), (21, 8), (32785, 7)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes17 : okE [] co17 (17, 12) = true := by decide +kernel
lemma lo17 : Imp [] 17 12 := imp_okE (e := (17, 12)) (Or.inl rfl) yes17 (addBound lo273 (addBound lo25 (addBound lo19 (addBound lo145 (addBound lo81 (addBound lo49 (addBound lo21 (addBound lo32785 emptyBounds))))))))
def co2048 : List (ℕ × ℕ) := []
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes2048 : okE [] co2048 (2048, 7) = true := by decide +kernel
lemma lo2048 : Imp [] 2048 7 := imp_okE (e := (2048, 7)) (Or.inl rfl) yes2048 emptyBounds
def co131072 : List (ℕ × ℕ) := [(131136, 7), (131088, 7), (131076, 7), (131073, 7)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes131072 : okE [] co131072 (131072, 8) = true := by decide +kernel
lemma lo131072 : Imp [] 131072 8 := imp_okE (e := (131072, 8)) (Or.inl rfl) yes131072 (addBound lo131136 (addBound lo131088 (addBound lo131076 (addBound lo131073 emptyBounds))))
def co32768 : List (ℕ × ℕ) := [(40960, 8), (33280, 8), (33024, 8), (32776, 8), (32770, 8), (41216, 7), (40968, 7), (40962, 7), (40961, 7), (33536, 7), (33296, 7), (33288, 7), (33282, 7), (33032, 7), (33026, 7), (32785, 7), (32778, 7)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes32768 : okE [] co32768 (32768, 9) = true := by decide +kernel
lemma lo32768 : Imp [] 32768 9 := imp_okE (e := (32768, 9)) (Or.inl rfl) yes32768 (addBound lo40960 (addBound lo33280 (addBound lo33024 (addBound lo32776 (addBound lo32770 (addBound lo41216 (addBound lo40968 (addBound lo40962 (addBound lo40961 (addBound lo33536 (addBound lo33296 (addBound lo33288 (addBound lo33282 (addBound lo33032 (addBound lo33026 (addBound lo32785 (addBound lo32778 emptyBounds)))))))))))))))))
def co1024 : List (ℕ × ℕ) := [(1088, 9), (1056, 9), (1032, 9), (66560, 8), (5120, 8), (1028, 8), (1040, 7), (1025, 7), (1120, 8), (1096, 8), (1064, 8), (66624, 7), (66592, 7), (66568, 7), (66564, 7), (5248, 7), (5184, 7), (5152, 7), (5124, 7), (1160, 7), (1092, 7), (1060, 7), (1128, 7)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes1024 : okE [] co1024 (1024, 10) = true := by decide +kernel
lemma lo1024 : Imp [] 1024 10 := imp_okE (e := (1024, 10)) (Or.inl rfl) yes1024 (addBound lo1088 (addBound lo1056 (addBound lo1032 (addBound lo66560 (addBound lo5120 (addBound lo1028 (addBound lo1040 (addBound lo1025 (addBound lo1120 (addBound lo1096 (addBound lo1064 (addBound lo66624 (addBound lo66592 (addBound lo66568 (addBound lo66564 (addBound lo5248 (addBound lo5184 (addBound lo5152 (addBound lo5124 (addBound lo1160 (addBound lo1092 (addBound lo1060 (addBound lo1128 emptyBounds)))))))))))))))))))))))
def co4096 : List (ℕ × ℕ) := [(4224, 9), (4160, 9), (4098, 9), (20480, 8), (5120, 8), (4100, 8), (4112, 7), (4097, 7), (4288, 8), (4226, 8), (4162, 8), (20608, 7), (20544, 7), (20484, 7), (20482, 7), (5248, 7), (5184, 7), (5152, 7), (5124, 7), (4228, 7), (4164, 7), (4130, 7), (4290, 7)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes4096 : okE [] co4096 (4096, 10) = true := by decide +kernel
lemma lo4096 : Imp [] 4096 10 := imp_okE (e := (4096, 10)) (Or.inl rfl) yes4096 (addBound lo4224 (addBound lo4160 (addBound lo4098 (addBound lo20480 (addBound lo5120 (addBound lo4100 (addBound lo4112 (addBound lo4097 (addBound lo4288 (addBound lo4226 (addBound lo4162 (addBound lo20608 (addBound lo20544 (addBound lo20484 (addBound lo20482 (addBound lo5248 (addBound lo5184 (addBound lo5152 (addBound lo5124 (addBound lo4228 (addBound lo4164 (addBound lo4130 (addBound lo4290 emptyBounds)))))))))))))))))))))))
def co16384 : List (ℕ × ℕ) := [(16512, 9), (16388, 9), (16386, 9), (20480, 8), (16392, 8), (16400, 7), (16385, 7), (16516, 8), (16514, 8), (16390, 8), (20608, 7), (20544, 7), (20484, 7), (20482, 7), (16520, 7), (16456, 7), (16396, 7), (16394, 7), (16518, 7)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes16384 : okE [] co16384 (16384, 10) = true := by decide +kernel
lemma lo16384 : Imp [] 16384 10 := imp_okE (e := (16384, 10)) (Or.inl rfl) yes16384 (addBound lo16512 (addBound lo16388 (addBound lo16386 (addBound lo20480 (addBound lo16392 (addBound lo16400 (addBound lo16385 (addBound lo16516 (addBound lo16514 (addBound lo16390 (addBound lo20608 (addBound lo20544 (addBound lo20484 (addBound lo20482 (addBound lo16520 (addBound lo16456 (addBound lo16396 (addBound lo16394 (addBound lo16518 emptyBounds)))))))))))))))))))
def co65536 : List (ℕ × ℕ) := [(65568, 9), (65544, 9), (65540, 9), (66560, 8), (65538, 8), (65552, 7), (65537, 7), (65576, 8), (65572, 8), (65548, 8), (66624, 7), (66592, 7), (66568, 7), (66564, 7), (65602, 7), (65570, 7), (65546, 7), (65542, 7), (65580, 7)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes65536 : okE [] co65536 (65536, 10) = true := by decide +kernel
lemma lo65536 : Imp [] 65536 10 := imp_okE (e := (65536, 10)) (Or.inl rfl) yes65536 (addBound lo65568 (addBound lo65544 (addBound lo65540 (addBound lo66560 (addBound lo65538 (addBound lo65552 (addBound lo65537 (addBound lo65576 (addBound lo65572 (addBound lo65548 (addBound lo66624 (addBound lo66592 (addBound lo66568 (addBound lo66564 (addBound lo65602 (addBound lo65570 (addBound lo65546 (addBound lo65542 (addBound lo65580 emptyBounds)))))))))))))))))))
def co256 : List (ℕ × ℕ) := [(8448, 10), (768, 10), (264, 9), (260, 9), (258, 9), (33024, 8), (320, 8), (8449, 9), (784, 9), (273, 9), (8456, 8), (8452, 8), (8450, 8), (776, 8), (772, 8), (770, 8), (41216, 7), (33536, 7), (33032, 7), (33026, 7), (8512, 7), (832, 7), (8457, 7), (8453, 7), (8451, 7), (792, 7), (788, 7), (786, 7)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes256 : okE [] co256 (256, 11) = true := by decide +kernel
lemma lo256 : Imp [] 256 11 := imp_okE (e := (256, 11)) (Or.inl rfl) yes256 (addBound lo8448 (addBound lo768 (addBound lo264 (addBound lo260 (addBound lo258 (addBound lo33024 (addBound lo320 (addBound lo8449 (addBound lo784 (addBound lo273 (addBound lo8456 (addBound lo8452 (addBound lo8450 (addBound lo776 (addBound lo772 (addBound lo770 (addBound lo41216 (addBound lo33536 (addBound lo33032 (addBound lo33026 (addBound lo8512 (addBound lo832 (addBound lo8457 (addBound lo8453 (addBound lo8451 (addBound lo792 (addBound lo788 (addBound lo786 emptyBounds))))))))))))))))))))))))))))
def co512 : List (ℕ × ℕ) := [(768, 10), (528, 10), (520, 9), (516, 9), (514, 9), (33280, 8), (576, 8), (640, 7), (544, 7), (784, 9), (776, 8), (772, 8), (770, 8), (536, 8), (532, 8), (530, 8), (33536, 7), (33296, 7), (33288, 7), (33282, 7), (832, 7), (592, 7), (584, 7), (578, 7), (792, 7), (788, 7), (786, 7)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes512 : okE [] co512 (512, 11) = true := by decide +kernel
lemma lo512 : Imp [] 512 11 := imp_okE (e := (512, 11)) (Or.inl rfl) yes512 (addBound lo768 (addBound lo528 (addBound lo520 (addBound lo516 (addBound lo514 (addBound lo33280 (addBound lo576 (addBound lo640 (addBound lo544 (addBound lo784 (addBound lo776 (addBound lo772 (addBound lo770 (addBound lo536 (addBound lo532 (addBound lo530 (addBound lo33536 (addBound lo33296 (addBound lo33288 (addBound lo33282 (addBound lo832 (addBound lo592 (addBound lo584 (addBound lo578 (addBound lo792 (addBound lo788 (addBound lo786 emptyBounds)))))))))))))))))))))))))))
def co8192 : List (ℕ × ℕ) := [(8448, 10), (8193, 10), (8200, 9), (8196, 9), (8194, 9), (40960, 8), (8256, 8), (8320, 7), (8224, 7), (8449, 9), (8456, 8), (8452, 8), (8450, 8), (8201, 8), (8197, 8), (8195, 8), (41216, 7), (40968, 7), (40962, 7), (40961, 7), (8512, 7), (8264, 7), (8258, 7), (8257, 7), (8457, 7), (8453, 7), (8451, 7)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes8192 : okE [] co8192 (8192, 11) = true := by decide +kernel
lemma lo8192 : Imp [] 8192 11 := imp_okE (e := (8192, 11)) (Or.inl rfl) yes8192 (addBound lo8448 (addBound lo8193 (addBound lo8200 (addBound lo8196 (addBound lo8194 (addBound lo40960 (addBound lo8256 (addBound lo8320 (addBound lo8224 (addBound lo8449 (addBound lo8456 (addBound lo8452 (addBound lo8450 (addBound lo8201 (addBound lo8197 (addBound lo8195 (addBound lo41216 (addBound lo40968 (addBound lo40962 (addBound lo40961 (addBound lo8512 (addBound lo8264 (addBound lo8258 (addBound lo8257 (addBound lo8457 (addBound lo8453 (addBound lo8451 emptyBounds)))))))))))))))))))))))))))
def co32 : List (ℕ × ℕ) := [(34, 11), (40, 10), (36, 10), (65568, 9), (1056, 9), (160, 9), (48, 9), (33, 9), (8224, 7), (544, 7), (65576, 8), (65572, 8), (1120, 8), (1064, 8), (168, 8), (164, 8), (162, 8), (98, 8), (50, 8), (49, 8), (42, 8), (38, 8), (35, 8), (66592, 7), (65570, 7), (5152, 7), (4130, 7), (1060, 7), (65580, 7), (1128, 7)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes32 : okE [] co32 (32, 12) = true := by decide +kernel
lemma lo32 : Imp [] 32 12 := imp_okE (e := (32, 12)) (Or.inl rfl) yes32 (addBound lo34 (addBound lo40 (addBound lo36 (addBound lo65568 (addBound lo1056 (addBound lo160 (addBound lo48 (addBound lo33 (addBound lo8224 (addBound lo544 (addBound lo65576 (addBound lo65572 (addBound lo1120 (addBound lo1064 (addBound lo168 (addBound lo164 (addBound lo162 (addBound lo98 (addBound lo50 (addBound lo49 (addBound lo42 (addBound lo38 (addBound lo35 (addBound lo66592 (addBound lo65570 (addBound lo5152 (addBound lo4130 (addBound lo1060 (addBound lo65580 (addBound lo1128 emptyBounds))))))))))))))))))))))))))))))
def co64 : List (ℕ × ℕ) := [(72, 11), (66, 11), (4160, 9), (1088, 9), (80, 9), (68, 9), (65, 9), (8256, 8), (576, 8), (320, 8), (131136, 7), (74, 10), (4288, 8), (4162, 8), (1120, 8), (1096, 8), (200, 8), (98, 8), (88, 8), (82, 8), (81, 8), (73, 8), (67, 8), (66624, 7), (65602, 7), (20544, 7), (16456, 7), (8512, 7), (8264, 7), (8258, 7), (8257, 7), (5184, 7), (4164, 7), (1092, 7), (832, 7), (592, 7), (584, 7), (578, 7), (4290, 7), (1128, 7)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes64 : okE [] co64 (64, 12) = true := by decide +kernel
lemma lo64 : Imp [] 64 12 := imp_okE (e := (64, 12)) (Or.inl rfl) yes64 (addBound lo72 (addBound lo66 (addBound lo4160 (addBound lo1088 (addBound lo80 (addBound lo68 (addBound lo65 (addBound lo8256 (addBound lo576 (addBound lo320 (addBound lo131136 (addBound lo74 (addBound lo4288 (addBound lo4162 (addBound lo1120 (addBound lo1096 (addBound lo200 (addBound lo98 (addBound lo88 (addBound lo82 (addBound lo81 (addBound lo73 (addBound lo67 (addBound lo66624 (addBound lo65602 (addBound lo20544 (addBound lo16456 (addBound lo8512 (addBound lo8264 (addBound lo8258 (addBound lo8257 (addBound lo5184 (addBound lo4164 (addBound lo1092 (addBound lo832 (addBound lo592 (addBound lo584 (addBound lo578 (addBound lo4290 (addBound lo1128 emptyBounds))))))))))))))))))))))))))))))))))))))))
def co128 : List (ℕ × ℕ) := [(136, 11), (132, 10), (130, 10), (16512, 9), (4224, 9), (160, 9), (144, 9), (129, 9), (8320, 7), (640, 7), (16516, 8), (16514, 8), (4288, 8), (4226, 8), (200, 8), (168, 8), (164, 8), (162, 8), (152, 8), (145, 8), (140, 8), (138, 8), (137, 8), (20608, 7), (16520, 7), (5248, 7), (4228, 7), (1160, 7), (16518, 7), (4290, 7)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes128 : okE [] co128 (128, 12) = true := by decide +kernel
lemma lo128 : Imp [] 128 12 := imp_okE (e := (128, 12)) (Or.inl rfl) yes128 (addBound lo136 (addBound lo132 (addBound lo130 (addBound lo16512 (addBound lo4224 (addBound lo160 (addBound lo144 (addBound lo129 (addBound lo8320 (addBound lo640 (addBound lo16516 (addBound lo16514 (addBound lo4288 (addBound lo4226 (addBound lo200 (addBound lo168 (addBound lo164 (addBound lo162 (addBound lo152 (addBound lo145 (addBound lo140 (addBound lo138 (addBound lo137 (addBound lo20608 (addBound lo16520 (addBound lo5248 (addBound lo4228 (addBound lo1160 (addBound lo16518 (addBound lo4290 emptyBounds))))))))))))))))))))))))))))))
def co1 : List (ℕ × ℕ) := [(17, 12), (9, 11), (3, 11), (8193, 10), (5, 10), (129, 9), (65, 9), (33, 9), (131073, 7), (65537, 7), (16385, 7), (4097, 7), (1025, 7), (8449, 9), (273, 9), (25, 9), (19, 9), (8201, 8), (8197, 8), (8195, 8), (145, 8), (137, 8), (81, 8), (73, 8), (67, 8), (49, 8), (35, 8), (21, 8), (11, 8), (40961, 7), (32785, 7), (8257, 7), (8457, 7), (8453, 7), (8451, 7)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes1 : okE [] co1 (1, 13) = true := by decide +kernel
lemma lo1 : Imp [] 1 13 := imp_okE (e := (1, 13)) (Or.inl rfl) yes1 (addBound lo17 (addBound lo9 (addBound lo3 (addBound lo8193 (addBound lo5 (addBound lo129 (addBound lo65 (addBound lo33 (addBound lo131073 (addBound lo65537 (addBound lo16385 (addBound lo4097 (addBound lo1025 (addBound lo8449 (addBound lo273 (addBound lo25 (addBound lo19 (addBound lo8201 (addBound lo8197 (addBound lo8195 (addBound lo145 (addBound lo137 (addBound lo81 (addBound lo73 (addBound lo67 (addBound lo49 (addBound lo35 (addBound lo21 (addBound lo11 (addBound lo40961 (addBound lo32785 (addBound lo8257 (addBound lo8457 (addBound lo8453 (addBound lo8451 emptyBounds)))))))))))))))))))))))))))))))))))
def co4 : List (ℕ × ℕ) := [(132, 10), (36, 10), (20, 10), (12, 10), (6, 10), (5, 10), (65540, 9), (16388, 9), (8196, 9), (516, 9), (260, 9), (68, 9), (4100, 8), (1028, 8), (131076, 7), (65572, 8), (65548, 8), (16516, 8), (16390, 8), (8452, 8), (8197, 8), (772, 8), (532, 8), (164, 8), (140, 8), (38, 8), (21, 8), (66564, 7), (65542, 7), (20484, 7), (16396, 7), (5124, 7), (4228, 7), (4164, 7), (1092, 7), (1060, 7), (65580, 7), (16518, 7), (8453, 7), (788, 7)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes4 : okE [] co4 (4, 13) = true := by decide +kernel
lemma lo4 : Imp [] 4 13 := imp_okE (e := (4, 13)) (Or.inl rfl) yes4 (addBound lo132 (addBound lo36 (addBound lo20 (addBound lo12 (addBound lo6 (addBound lo5 (addBound lo65540 (addBound lo16388 (addBound lo8196 (addBound lo516 (addBound lo260 (addBound lo68 (addBound lo4100 (addBound lo1028 (addBound lo131076 (addBound lo65572 (addBound lo65548 (addBound lo16516 (addBound lo16390 (addBound lo8452 (addBound lo8197 (addBound lo772 (addBound lo532 (addBound lo164 (addBound lo140 (addBound lo38 (addBound lo21 (addBound lo66564 (addBound lo65542 (addBound lo20484 (addBound lo16396 (addBound lo5124 (addBound lo4228 (addBound lo4164 (addBound lo1092 (addBound lo1060 (addBound lo65580 (addBound lo16518 (addBound lo8453 (addBound lo788 emptyBounds))))))))))))))))))))))))))))))))))))))))
def co16 : List (ℕ × ℕ) := [(17, 12), (24, 11), (18, 11), (528, 10), (20, 10), (144, 9), (80, 9), (48, 9), (131088, 7), (65552, 7), (16400, 7), (4112, 7), (1040, 7), (784, 9), (273, 9), (25, 9), (19, 9), (536, 8), (532, 8), (530, 8), (152, 8), (145, 8), (88, 8), (82, 8), (81, 8), (50, 8), (49, 8), (26, 8), (21, 8), (33296, 7), (32785, 7), (592, 7), (792, 7), (788, 7), (786, 7)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes16 : okE [] co16 (16, 13) = true := by decide +kernel
lemma lo16 : Imp [] 16 13 := imp_okE (e := (16, 13)) (Or.inl rfl) yes16 (addBound lo17 (addBound lo24 (addBound lo18 (addBound lo528 (addBound lo20 (addBound lo144 (addBound lo80 (addBound lo48 (addBound lo131088 (addBound lo65552 (addBound lo16400 (addBound lo4112 (addBound lo1040 (addBound lo784 (addBound lo273 (addBound lo25 (addBound lo19 (addBound lo536 (addBound lo532 (addBound lo530 (addBound lo152 (addBound lo145 (addBound lo88 (addBound lo82 (addBound lo81 (addBound lo50 (addBound lo49 (addBound lo26 (addBound lo21 (addBound lo33296 (addBound lo32785 (addBound lo592 (addBound lo792 (addBound lo788 (addBound lo786 emptyBounds)))))))))))))))))))))))))))))))))))
def co2 : List (ℕ × ℕ) := [(66, 11), (34, 11), (18, 11), (10, 11), (3, 11), (130, 10), (6, 10), (16386, 9), (8194, 9), (4098, 9), (514, 9), (258, 9), (65538, 8), (32770, 8), (74, 10), (19, 9), (16514, 8), (16390, 8), (8450, 8), (8195, 8), (4226, 8), (4162, 8), (770, 8), (530, 8), (162, 8), (138, 8), (98, 8), (82, 8), (67, 8), (50, 8), (42, 8), (38, 8), (35, 8), (26, 8), (11, 8), (65602, 7), (65570, 7), (65546, 7), (65542, 7), (40962, 7), (33282, 7), (33026, 7), (32778, 7), (20482, 7), (16394, 7), (8258, 7), (4130, 7), (578, 7), (16518, 7), (8451, 7), (4290, 7), (786, 7)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes2 : okE [] co2 (2, 14) = true := by decide +kernel
lemma lo2 : Imp [] 2 14 := imp_okE (e := (2, 14)) (Or.inl rfl) yes2 (addBound lo66 (addBound lo34 (addBound lo18 (addBound lo10 (addBound lo3 (addBound lo130 (addBound lo6 (addBound lo16386 (addBound lo8194 (addBound lo4098 (addBound lo514 (addBound lo258 (addBound lo65538 (addBound lo32770 (addBound lo74 (addBound lo19 (addBound lo16514 (addBound lo16390 (addBound lo8450 (addBound lo8195 (addBound lo4226 (addBound lo4162 (addBound lo770 (addBound lo530 (addBound lo162 (addBound lo138 (addBound lo98 (addBound lo82 (addBound lo67 (addBound lo50 (addBound lo42 (addBound lo38 (addBound lo35 (addBound lo26 (addBound lo11 (addBound lo65602 (addBound lo65570 (addBound lo65546 (addBound lo65542 (addBound lo40962 (addBound lo33282 (addBound lo33026 (addBound lo32778 (addBound lo20482 (addBound lo16394 (addBound lo8258 (addBound lo4130 (addBound lo578 (addBound lo16518 (addBound lo8451 (addBound lo4290 (addBound lo786 emptyBounds))))))))))))))))))))))))))))))))))))))))))))))))))))
def co8 : List (ℕ × ℕ) := [(136, 11), (72, 11), (24, 11), (10, 11), (9, 11), (40, 10), (12, 10), (65544, 9), (8200, 9), (1032, 9), (520, 9), (264, 9), (32776, 8), (16392, 8), (74, 10), (25, 9), (65576, 8), (65548, 8), (8456, 8), (8201, 8), (1096, 8), (1064, 8), (776, 8), (536, 8), (200, 8), (168, 8), (152, 8), (140, 8), (138, 8), (137, 8), (88, 8), (73, 8), (42, 8), (26, 8), (11, 8), (66568, 7), (65546, 7), (40968, 7), (33288, 7), (33032, 7), (32778, 7), (16520, 7), (16456, 7), (16396, 7), (16394, 7), (8264, 7), (1160, 7), (584, 7), (65580, 7), (8457, 7), (1128, 7), (792, 7)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem yes8 : okE [] co8 (8, 14) = true := by decide +kernel
lemma lo8 : Imp [] 8 14 := imp_okE (e := (8, 14)) (Or.inl rfl) yes8 (addBound lo136 (addBound lo72 (addBound lo24 (addBound lo10 (addBound lo9 (addBound lo40 (addBound lo12 (addBound lo65544 (addBound lo8200 (addBound lo1032 (addBound lo520 (addBound lo264 (addBound lo32776 (addBound lo16392 (addBound lo74 (addBound lo25 (addBound lo65576 (addBound lo65548 (addBound lo8456 (addBound lo8201 (addBound lo1096 (addBound lo1064 (addBound lo776 (addBound lo536 (addBound lo200 (addBound lo168 (addBound lo152 (addBound lo140 (addBound lo138 (addBound lo137 (addBound lo88 (addBound lo73 (addBound lo42 (addBound lo26 (addBound lo11 (addBound lo66568 (addBound lo65546 (addBound lo40968 (addBound lo33288 (addBound lo33032 (addBound lo32778 (addBound lo16520 (addBound lo16456 (addBound lo16396 (addBound lo16394 (addBound lo8264 (addBound lo1160 (addBound lo584 (addBound lo65580 (addBound lo8457 (addBound lo1128 (addBound lo792 emptyBounds))))))))))))))))))))))))))))))))))))))))))))))))))))
def useful : List (ℕ × ℕ) := [(8, 14), (2, 14), (16, 13), (4, 13), (1, 13), (128, 12), (64, 12), (32, 12), (8192, 11), (512, 11), (256, 11), (65536, 10), (16384, 10), (4096, 10), (1024, 10), (32768, 9), (17, 12), (136, 11), (72, 11), (66, 11), (34, 11), (24, 11), (18, 11), (10, 11), (9, 11), (3, 11), (8448, 10), (8193, 10), (768, 10), (528, 10), (132, 10), (130, 10), (40, 10), (36, 10), (20, 10), (12, 10), (6, 10), (5, 10), (65568, 9), (65544, 9), (65540, 9), (16512, 9), (16388, 9), (16386, 9), (8200, 9), (8196, 9), (8194, 9), (4224, 9), (4160, 9), (4098, 9), (1088, 9), (1056, 9), (1032, 9), (520, 9), (516, 9), (514, 9), (264, 9), (260, 9), (258, 9), (160, 9), (144, 9), (129, 9), (80, 9), (68, 9), (65, 9), (48, 9), (33, 9)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem useful_lower : ∀ e ∈ useful, Imp [] e.1 e.2 := (addBound lo8 (addBound lo2 (addBound lo16 (addBound lo4 (addBound lo1 (addBound lo128 (addBound lo64 (addBound lo32 (addBound lo8192 (addBound lo512 (addBound lo256 (addBound lo65536 (addBound lo16384 (addBound lo4096 (addBound lo1024 (addBound lo32768 (addBound lo17 (addBound lo136 (addBound lo72 (addBound lo66 (addBound lo34 (addBound lo24 (addBound lo18 (addBound lo10 (addBound lo9 (addBound lo3 (addBound lo8448 (addBound lo8193 (addBound lo768 (addBound lo528 (addBound lo132 (addBound lo130 (addBound lo40 (addBound lo36 (addBound lo20 (addBound lo12 (addBound lo6 (addBound lo5 (addBound lo65568 (addBound lo65544 (addBound lo65540 (addBound lo16512 (addBound lo16388 (addBound lo16386 (addBound lo8200 (addBound lo8196 (addBound lo8194 (addBound lo4224 (addBound lo4160 (addBound lo4098 (addBound lo1088 (addBound lo1056 (addBound lo1032 (addBound lo520 (addBound lo516 (addBound lo514 (addBound lo264 (addBound lo260 (addBound lo258 (addBound lo160 (addBound lo144 (addBound lo129 (addBound lo80 (addBound lo68 (addBound lo65 (addBound lo48 (addBound lo33 emptyBounds)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
def scopes : List (ℕ × ℕ × ℕ) := [(15, FF, 1), (14, FF, 1), (13, FF, 1), (12, FF, 1), (11, FF, 1), (10, FF, 1), (9, FF, 1), (8, FF, 1), (7, FF, 1), (6, FF, 1), (5, FF, 1), (4, FF, 1), (3, 0x10101010101010101010101010101010101010101010101010101, 1), (3, 0x20202020202020202020202020202020202020202020202020202, 0), (3, 0x40404040404040404040404040404040404040404040404040404, 0), (3, 0x80808080808080808080808080808080808080808080808080808, 0), (3, 0x101010101010101010101010101010101010101010101010101010, 0), (3, 0x202020202020202020202020202020202020202020202020202020, 0), (3, 0x4040404040404040404040404040404040404040404040404040, 0), (3, 0x8080808080808080808080808080808080808080808080808080, 0), (2, 0x10101010101010101010101010101010101010101010101010101, 1), (2, 0x20202020202020202020202020202020202020202020202020202, 0), (2, 0x40404040404040404040404040404040404040404040404040404, 0), (2, 0x80808080808080808080808080808080808080808080808080808, 0), (2, 0x101010101010101010101010101010101010101010101010101010, 0), (2, 0x202020202020202020202020202020202020202020202020202020, 0), (2, 0x4040404040404040404040404040404040404040404040404040, 0), (2, 0x8080808080808080808080808080808080808080808080808080, 0), (1, 0x10101010101010101010101010101010101010101010101010101, 1), (1, 0x20202020202020202020202020202020202020202020202020202, 0), (1, 0x40404040404040404040404040404040404040404040404040404, 0), (1, 0x80808080808080808080808080808080808080808080808080808, 0), (1, 0x101010101010101010101010101010101010101010101010101010, 0), (1, 0x202020202020202020202020202020202020202020202020202020, 0), (1, 0x4040404040404040404040404040404040404040404040404040, 0), (1, 0x8080808080808080808080808080808080808080808080808080, 0), (0, 0x10101010101010101010101010101010101010101010101010101, 1), (0, 0x20202020202020202020202020202020202020202020202020202, 0), (0, 0x40404040404040404040404040404040404040404040404040404, 0), (0, 0x80808080808080808080808080808080808080808080808080808, 0), (0, 0x101010101010101010101010101010101010101010101010101010, 0), (0, 0x202020202020202020202020202020202020202020202020202020, 0), (0, 0x4040404040404040404040404040404040404040404040404040, 0), (0, 0x8080808080808080808080808080808080808080808080808080, 0)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem case15_0 : okS useful 0 15 (15, FF, 1) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem case14_0 : okS useful 0 15 (14, FF, 1) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem case13_0 : okS useful 0 15 (13, FF, 1) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem case12_0 : okS useful 0 15 (12, FF, 1) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem case11_0 : okS useful 0 15 (11, FF, 1) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem case10_0 : okS useful 0 15 (10, FF, 1) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem case9_0 : okS useful 0 15 (9, FF, 1) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem case8_0 : okS useful 0 15 (8, FF, 1) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem case7_0 : okS useful 0 15 (7, FF, 1) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem case6_0 : okS useful 0 15 (6, FF, 1) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem case5_0 : okS useful 0 15 (5, FF, 1) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem case4_0 : okS useful 0 15 (4, FF, 1) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem case3_0 : okS useful 0 15 (3, 0x10101010101010101010101010101010101010101010101010101, 1) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem case3_1 : okS useful 0 15 (3, 0x20202020202020202020202020202020202020202020202020202, 0) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem case3_2 : okS useful 0 15 (3, 0x40404040404040404040404040404040404040404040404040404, 0) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem case3_3 : okS useful 0 15 (3, 0x80808080808080808080808080808080808080808080808080808, 0) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem case3_4 : okS useful 0 15 (3, 0x101010101010101010101010101010101010101010101010101010, 0) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem case3_5 : okS useful 0 15 (3, 0x202020202020202020202020202020202020202020202020202020, 0) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem case3_6 : okS useful 0 15 (3, 0x4040404040404040404040404040404040404040404040404040, 0) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem case3_7 : okS useful 0 15 (3, 0x8080808080808080808080808080808080808080808080808080, 0) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem case2_0 : okS useful 0 15 (2, 0x10101010101010101010101010101010101010101010101010101, 1) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem case2_1 : okS useful 0 15 (2, 0x20202020202020202020202020202020202020202020202020202, 0) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem case2_2 : okS useful 0 15 (2, 0x40404040404040404040404040404040404040404040404040404, 0) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem case2_3 : okS useful 0 15 (2, 0x80808080808080808080808080808080808080808080808080808, 0) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem case2_4 : okS useful 0 15 (2, 0x101010101010101010101010101010101010101010101010101010, 0) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem case2_5 : okS useful 0 15 (2, 0x202020202020202020202020202020202020202020202020202020, 0) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem case2_6 : okS useful 0 15 (2, 0x4040404040404040404040404040404040404040404040404040, 0) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem case2_7 : okS useful 0 15 (2, 0x8080808080808080808080808080808080808080808080808080, 0) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem case1_0 : okS useful 0 15 (1, 0x10101010101010101010101010101010101010101010101010101, 1) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem case1_1 : okS useful 0 15 (1, 0x20202020202020202020202020202020202020202020202020202, 0) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem case1_2 : okS useful 0 15 (1, 0x40404040404040404040404040404040404040404040404040404, 0) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem case1_3 : okS useful 0 15 (1, 0x80808080808080808080808080808080808080808080808080808, 0) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem case1_4 : okS useful 0 15 (1, 0x101010101010101010101010101010101010101010101010101010, 0) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem case1_5 : okS useful 0 15 (1, 0x202020202020202020202020202020202020202020202020202020, 0) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem case1_6 : okS useful 0 15 (1, 0x4040404040404040404040404040404040404040404040404040, 0) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem case1_7 : okS useful 0 15 (1, 0x8080808080808080808080808080808080808080808080808080, 0) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem case0_0 : okS useful 0 15 (0, 0x10101010101010101010101010101010101010101010101010101, 1) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem case0_1 : okS useful 0 15 (0, 0x20202020202020202020202020202020202020202020202020202, 0) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem case0_2 : okS useful 0 15 (0, 0x40404040404040404040404040404040404040404040404040404, 0) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem case0_3 : okS useful 0 15 (0, 0x80808080808080808080808080808080808080808080808080808, 0) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem case0_4 : okS useful 0 15 (0, 0x101010101010101010101010101010101010101010101010101010, 0) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem case0_5 : okS useful 0 15 (0, 0x202020202020202020202020202020202020202020202020202020, 0) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem case0_6 : okS useful 0 15 (0, 0x4040404040404040404040404040404040404040404040404040, 0) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem case0_7 : okS useful 0 15 (0, 0x8080808080808080808080808080808080808080808080808080, 0) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cases_ok : scopes.all (okS useful 0 15) = true := by simp [scopes, case15_0, case14_0, case13_0, case12_0, case11_0, case10_0, case9_0, case8_0, case7_0, case6_0, case5_0, case4_0, case3_0, case3_1, case3_2, case3_3, case3_4, case3_5, case3_6, case3_7, case2_0, case2_1, case2_2, case2_3, case2_4, case2_5, case2_6, case2_7, case1_0, case1_1, case1_2, case1_3, case1_4, case1_5, case1_6, case1_7, case0_0, case0_1, case0_2, case0_3, case0_4, case0_5, case0_6, case0_7]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem scopes_ok : okP useful 0 16 scopes = true := by decide +kernel
theorem impossible : Imp [] 0 16 := imp_run scopes useful_lower scopes_ok cases_ok
end PEqualNP.Outside.L_meta_11040

open PEqualNP.Outside.L_meta_11040 in
theorem PEqualNP.Outside.L_meta_11040 : ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 9 (fun x : Fin 9 → Bool => (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 5) || (x 1 && x 6) || (x 3 && x 6) || (x 2 && x 7) || (x 3 && x 7) || (x 5 && x 7) || (x 0 && x 8) || (x 2 && x 8) || (x 4 && x 8) || (x 6 && x 8)) t → 16 ≤ t := by
  rintro t ⟨C, hc, hs, hf⟩
  by_contra! h
  exact impossible C.size (by omega) (bridge C hc hf)
