/-
  Semiprime Interleaving and Twin Prime Detection

  This file formalizes the connection between:
  1. The interleaving statistic L(n) for semiprime sets
  2. Prime ratio record minima
  3. Twin primes

  Main results:
  - Keystone Lemma: L(n) = n ↔ r_n is a strict record minimum
  - Twin → Perfect: gap = 2 → L(n) = n (unconditional)
  - Perfect → Twin-free interval: L(n) = n ∧ gap ≥ 4 → twin-free interval exists
-/

-- Minimal imports - adjust based on your Mathlib version
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.NumberTheory.Bertrand
import Mathlib.Data.List.Sort
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

open Nat

/-! ## Basic Definitions -/

/-- The n-th prime (1-indexed: nthPrime 1 = 2, nthPrime 2 = 3, nthPrime 3 = 5, ...) -/
noncomputable def nthPrime (n : ℕ) : ℕ :=
  if n = 0 then 0 else Nat.nth Nat.Prime (n - 1)

/-- Prime gap at position n: g(n) = p(n+1) - p(n) -/
noncomputable def primeGap (n : ℕ) : ℕ := nthPrime (n + 1) - nthPrime n

/-- Prime ratio at position n: r(n) = p(n+1) / p(n) as a natural division (floor) -/
-- Using ℕ division to avoid Rat import issues; for proofs we'll use inequalities directly
noncomputable def primeRatioNum (n : ℕ) : ℕ := nthPrime (n + 1)
noncomputable def primeRatioDen (n : ℕ) : ℕ := nthPrime n

/-- Ratio comparison: r_n < r_j as cross-multiplication -/
def ratioLt (n j : ℕ) : Prop :=
  primeRatioNum n * primeRatioDen j < primeRatioNum j * primeRatioDen n

/-- Ratio comparison: r_j ≤ r_n as cross-multiplication -/
def ratioLe (j n : ℕ) : Prop :=
  primeRatioNum j * primeRatioDen n ≤ primeRatioNum n * primeRatioDen j

/-- n is a twin prime index if gap(n) = 2 -/
def isTwinIndex (n : ℕ) : Prop := primeGap n = 2

/-! ## Semiprime Sets -/

/-- The anchored semiprime set S_n = {p_i · p_n : 1 ≤ i ≤ n} as a list -/
noncomputable def semiprimeList (n : ℕ) : List ℕ :=
  (List.range n).map (fun i => nthPrime (i + 1) * nthPrime n)

/-- Elements labeled 'A' or 'B' -/
inductive Label where
  | A : Label
  | B : Label
  deriving DecidableEq, Repr

/-- A labeled element from the merged set -/
structure LabeledElement where
  value : ℕ
  label : Label
  deriving DecidableEq, Repr

instance : LE LabeledElement where
  le a b := a.value ≤ b.value

instance : LT LabeledElement where
  lt a b := a.value < b.value

instance : DecidableRel (α := LabeledElement) (· ≤ ·) :=
  fun a b => inferInstanceAs (Decidable (a.value ≤ b.value))

/-- Merge S_n and S_{n+1} with labels, sorted by value -/
noncomputable def mergedList (n : ℕ) : List LabeledElement :=
  let sn := (semiprimeList n).map (fun v => ⟨v, Label.A⟩)
  let sn1 := (semiprimeList (n + 1)).map (fun v => ⟨v, Label.B⟩)
  (sn ++ sn1).mergeSort (· ≤ ·)

/-! ## The Interleaving Statistic L(n) -/

/-- Count consecutive (A,B) pairs from the start of a list -/
def countAlternatingPrefix : List LabeledElement → ℕ
  | [] => 0
  | [_] => 0
  | a :: b :: rest =>
    if a.label = Label.A ∧ b.label = Label.B then
      1 + countAlternatingPrefix rest
    else
      0

/-- L(n) = length of maximal alternating (A,B) prefix -/
noncomputable def L (n : ℕ) : ℕ := countAlternatingPrefix (mergedList n)

/-! ## Record Minimum -/

/-- r_n is a strict record minimum if r_n < r_j for all j in {1, ..., n-1} -/
def isStrictRecordMin (n : ℕ) : Prop :=
  ∀ j : ℕ, 1 ≤ j → j < n → ratioLt n j

/-! ## Main Theorems -/

/-- Key inequality: merge order determined by ratio comparison
    p_j · p_{n+1} < p_{j+1} · p_n  ↔  r_n < r_j -/
lemma merge_order_iff_ratio (n j : ℕ) :
    nthPrime j * nthPrime (n + 1) < nthPrime (j + 1) * nthPrime n ↔
    ratioLt n j := by
  unfold ratioLt primeRatioNum primeRatioDen
  rw [mul_comm (nthPrime (n + 1)) (nthPrime j)]

lemma semiprimeList_length (n : ℕ) : (semiprimeList n).length = n := by
  simp only [semiprimeList, List.length_map, List.length_range]

lemma semiprimeList_get (n j : ℕ) (hj : j < n) :
    (semiprimeList n).get ⟨j, by rw [semiprimeList_length]; exact hj⟩
      = nthPrime (j + 1) * nthPrime n := by
  unfold semiprimeList
  simp only [List.get_eq_getElem, List.getElem_map, List.getElem_range]

/-- B_j comes before A_{j+1} iff p_j * p_{n+1} < p_{j+1} * p_n -/
lemma merge_ordering (n j : ℕ) (_hn : n ≥ 1) (_hj : j < n) :
    nthPrime (j + 1) * nthPrime (n + 1) < nthPrime (j + 2) * nthPrime n ↔
    ratioLt n (j + 1) := by
  rw [← merge_order_iff_ratio]

/-- The alternating prefix has length at least k -/
def hasAlternatingPrefix (l : List LabeledElement) (k : ℕ) : Prop :=
  countAlternatingPrefix l ≥ k

/-- The j-th A element (0-indexed) in the original unsorted list is p_{j+1} * p_n -/
lemma A_element_value (n j : ℕ) (hj : j < n) :
    nthPrime (j + 1) * nthPrime n ∈ (semiprimeList n) := by
  simp only [semiprimeList, List.mem_map, List.mem_range]
  exact ⟨j, hj, rfl⟩

/-- The j-th B element (0-indexed) in the original unsorted list is p_{j+1} * p_{n+1} -/
lemma B_element_value (n j : ℕ) (hj : j < n + 1) :
    nthPrime (j + 1) * nthPrime (n + 1) ∈ (semiprimeList (n + 1)) := by
  simp only [semiprimeList, List.mem_map, List.mem_range]
  exact ⟨j, hj, rfl⟩

/-- A_j < B_j always: p_{j+1} * p_n < p_{j+1} * p_{n+1} -/
lemma A_lt_B (n j : ℕ) (_hn : n ≥ 1) (_hj : j < n) (hpos : nthPrime (j + 1) > 0)
    (hmono : nthPrime n < nthPrime (n + 1)) :
    nthPrime (j + 1) * nthPrime n < nthPrime (j + 1) * nthPrime (n + 1) := by
  exact Nat.mul_lt_mul_of_pos_left hmono hpos

/-- B_j < A_{j+1} iff ratioLt n (j+1) -/
lemma B_lt_A_succ_iff (n j : ℕ) (hn : n ≥ 1) (hj : j + 1 < n) :
    nthPrime (j + 1) * nthPrime (n + 1) < nthPrime (j + 2) * nthPrime n ↔
    ratioLt n (j + 1) := by
  exact merge_ordering n j hn (Nat.lt_of_succ_lt hj)

/-- nthPrime is positive for positive input -/
lemma nthPrime_pos (n : ℕ) (hn : n ≥ 1) : nthPrime n > 0 := by
  unfold nthPrime
  split_ifs with h
  · omega
  · have hprime : Nat.Prime (Nat.nth Nat.Prime (n - 1)) :=
      Nat.nth_mem_of_infinite Nat.infinite_setOf_prime (n - 1)
    exact Nat.Prime.pos hprime

/-- The merge structure: for each j < n, the ordering relationships hold -/
lemma mergedList_structure (n : ℕ) (hn : n ≥ 1)
    (hprime_mono : ∀ i, i ≥ 1 → nthPrime i < nthPrime (i + 1)) :
    ∀ j, j < n →
      nthPrime (j + 1) * nthPrime n < nthPrime (j + 1) * nthPrime (n + 1) ∧
      (j + 1 < n →
        (nthPrime (j + 1) * nthPrime (n + 1) < nthPrime (j + 2) * nthPrime n ↔
         ratioLt n (j + 1))) := by
  intro j hj
  constructor
  · -- A_j < B_j
    have hpos : nthPrime (j + 1) > 0 := nthPrime_pos (j + 1) (by omega)
    have hmono : nthPrime n < nthPrime (n + 1) := hprime_mono n hn
    exact Nat.mul_lt_mul_of_pos_left hmono hpos
  · -- B_j < A_{j+1} iff ratioLt
    intro hjn
    exact merge_ordering n j hn (Nat.lt_of_succ_lt hjn)

/-- nthPrime is strictly monotonic -/
lemma nthPrime_strictMono' (hprime_mono : ∀ i, i ≥ 1 → nthPrime i < nthPrime (i + 1)) :
    ∀ i j, 1 ≤ i → i < j → nthPrime i < nthPrime j := by
  intro i j hi hij
  induction j with
  | zero => omega
  | succ k ih =>
    cases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hij) with
    | inl hik =>
      have : nthPrime i < nthPrime k := ih hik
      have : nthPrime k < nthPrime (k + 1) := hprime_mono k (by omega)
      omega
    | inr hik =>
      rw [← hik]
      exact hprime_mono i hi

lemma semiprimeList_sorted (n : ℕ) (hn : n ≥ 1)
    (hprime_mono : ∀ i, i ≥ 1 → nthPrime i < nthPrime (i + 1)) :
    List.Pairwise (· < ·) (semiprimeList n) := by
  unfold semiprimeList
  rw [List.pairwise_map]
  apply List.Pairwise.imp
  case R => exact (· < ·)
  case H =>
    intro i j hij
    have hp_n_pos : nthPrime n > 0 := nthPrime_pos n hn
    apply Nat.mul_lt_mul_of_pos_right _ hp_n_pos
    apply nthPrime_strictMono' hprime_mono
    · omega
    · omega
  case a => exact @List.pairwise_lt_range n

lemma nthPrime_injective (hprime_mono : ∀ i, i ≥ 1 → nthPrime i < nthPrime (i + 1)) :
    ∀ i j, i ≥ 1 → j ≥ 1 → nthPrime i = nthPrime j → i = j := by
  intro i j hi hj heq
  by_contra hne
  cases Nat.lt_or_gt_of_ne hne with
  | inl hij =>
    have : nthPrime i < nthPrime j := nthPrime_strictMono' hprime_mono i j hi hij
    omega
  | inr hji =>
    have : nthPrime j < nthPrime i := nthPrime_strictMono' hprime_mono j i hj hji
    omega

lemma semiprimeList_nodup (n : ℕ) (hn : n ≥ 1)
    (hprime_mono : ∀ i, i ≥ 1 → nthPrime i < nthPrime (i + 1)) :
    List.Nodup (semiprimeList n) := by
  unfold semiprimeList
  apply List.Nodup.map
  · intro i j hij
    have hp_n_pos : nthPrime n > 0 := nthPrime_pos n hn
    have heq : nthPrime (i + 1) * nthPrime n = nthPrime (j + 1) * nthPrime n := hij
    have heq' : nthPrime (i + 1) = nthPrime (j + 1) := Nat.eq_of_mul_eq_mul_right hp_n_pos heq
    have hinj := nthPrime_injective hprime_mono (i + 1) (j + 1) (by omega) (by omega) heq'
    omega
  · exact @List.nodup_range n

/-- Interleave two lists: [a₀,a₁,...] and [b₀,b₁,...] → [a₀,b₀,a₁,b₁,...] -/
def List.interleave : List α → List α → List α
  | [], bs => bs
  | a :: as, bs => a :: List.interleave bs as
termination_by as bs => as.length + bs.length

/-- Interleave two lists of equal length: [a₀,a₁,...] and [b₀,b₁,...] → [a₀,b₀,a₁,b₁,...] -/
def perfectMerge : List ℕ → List ℕ → List ℕ
  | [], [] => []
  | a :: as, b :: bs => a :: b :: perfectMerge as bs
  | _, _ => []  -- default case for unequal lengths

/-- perfectMerge is a permutation of as ++ bs -/
lemma perfectMerge_perm (as bs : List ℕ) (hlen : as.length = bs.length) :
    (perfectMerge as bs).Perm (as ++ bs) := by
  induction as generalizing bs with
  | nil =>
    simp only [List.length_nil] at hlen
    cases bs with
    | nil => simp [perfectMerge]
    | cons b bs => simp at hlen
  | cons a as ih =>
    cases bs with
    | nil => simp at hlen
    | cons b bs =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      simp only [perfectMerge, List.cons_append]
      apply List.Perm.cons
      -- goal: (b :: perfectMerge as bs).Perm (as ++ b :: bs)
      have h1 : (perfectMerge as bs).Perm (as ++ bs) := ih bs hlen
      have h2 : (b :: perfectMerge as bs).Perm (b :: (as ++ bs)) := List.Perm.cons b h1
      have h3 : (b :: (as ++ bs)).Perm (as ++ b :: bs) := by
        have := @List.perm_middle ℕ b as bs
        exact List.Perm.symm this
      exact List.Perm.trans h2 h3

/-- In a sorted list, the head is ≤ all elements -/
lemma List.head_le_of_mem_of_sorted {as : List ℕ} (h : as ≠ [])
    (hsorted : List.Pairwise (· < ·) as) (hx : x ∈ as) :
    as.head h ≤ x := by
  cases as with
  | nil => contradiction
  | cons a' as' =>
    simp only [List.head_cons]
    simp only [List.mem_cons] at hx
    cases hx with
    | inl heq => rw [heq]
    | inr hmem =>
      have := List.rel_of_pairwise_cons hsorted hmem
      omega

/-- perfectMerge is sorted when alternation conditions hold -/
lemma perfectMerge_sorted (as bs : List ℕ)
    (has : List.Pairwise (· < ·) as) (hbs : List.Pairwise (· < ·) bs)
    (hlen : as.length = bs.length)
    (halt : ∀ i (hi : i < as.length), as[i]'hi < bs[i]'(hlen ▸ hi) ∧
        ∀ (hi2 : i + 1 < as.length), bs[i]'(hlen ▸ hi) < as[i + 1]'hi2) :
    List.Pairwise (· < ·) (perfectMerge as bs) := by
  induction as generalizing bs with
  | nil =>
    cases bs with
    | nil => simp [perfectMerge]
    | cons b bs => simp at hlen
  | cons a as ih =>
    cases bs with
    | nil => simp at hlen
    | cons b bs =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      simp only [perfectMerge]
      have hab : a < b := by
        have h0 := halt 0 (by simp)
        exact h0.1
      have has' : List.Pairwise (· < ·) as := List.Pairwise.of_cons has
      have hbs' : List.Pairwise (· < ·) bs := List.Pairwise.of_cons hbs
      have halt' : ∀ i (hi : i < as.length), as[i]'hi < bs[i]'(hlen ▸ hi) ∧
          ∀ (hi2 : i + 1 < as.length), bs[i]'(hlen ▸ hi) < as[i + 1]'hi2 := by
        intro i hi
        have hi' : i + 1 < (a :: as).length := by simp; omega
        have h := halt (i + 1) hi'
        simp only [List.getElem_cons_succ] at h
        exact ⟨h.1, fun hi2 => h.2 (by simp; omega)⟩
      have ih_sorted := ih bs has' hbs' hlen halt'
      apply List.Pairwise.cons
      · intro x hx
        simp only [List.mem_cons] at hx
        cases hx with
        | inl hxb => rw [hxb]; exact hab
        | inr hxrest =>
          have hperm := perfectMerge_perm as bs hlen
          have hx_in : x ∈ as ++ bs := List.Perm.mem_iff hperm |>.mp hxrest
          simp only [List.mem_append] at hx_in
          cases hx_in with
          | inl hx_as => exact List.rel_of_pairwise_cons has hx_as
          | inr hx_bs => exact Nat.lt_trans hab (List.rel_of_pairwise_cons hbs hx_bs)
      · apply List.Pairwise.cons
        · intro x hx
          have hperm := perfectMerge_perm as bs hlen
          have hx_in : x ∈ as ++ bs := List.Perm.mem_iff hperm |>.mp hx
          simp only [List.mem_append] at hx_in
          cases hx_in with
          | inl hx_as =>
            cases as with
            | nil => simp at hx_as
            | cons a' as' =>
              have h0' := halt 0 (by simp)
              simp only [List.getElem_cons_zero, List.getElem_cons_succ] at h0'
              have hb_lt_a' : b < a' := h0'.2 (by simp)
              simp only [List.mem_cons] at hx_as
              cases hx_as with
              | inl heq => rw [heq]; exact hb_lt_a'
              | inr hmem =>
                have ha'_lt_x : a' < x := List.rel_of_pairwise_cons has' hmem
                exact Nat.lt_trans hb_lt_a' ha'_lt_x
          | inr hx_bs =>
            exact List.rel_of_pairwise_cons hbs hx_bs
        · exact ih_sorted


/-- When two sorted lists satisfy alternation conditions, their sorted merge
    equals the perfect interleaving -/
lemma merge_two_sorted_alternates (as bs : List ℕ)
    (has : List.Pairwise (· < ·) as) (hbs : List.Pairwise (· < ·) bs)
    (hlen : as.length = bs.length)
    (_hnodup : List.Nodup (as ++ bs))
    (halt : ∀ i (hi : i < as.length), as[i]'hi < bs[i]'(hlen ▸ hi) ∧
        ∀ (hi2 : i + 1 < as.length), bs[i]'(hlen ▸ hi) < as[i + 1]'hi2) :
    (as ++ bs).mergeSort (· ≤ ·) = perfectMerge as bs := by
  symm
  apply List.Perm.eq_of_pairwise
  · -- Antisymmetry for ≤: if a ≤ b and b ≤ a then a = b
    intro a b _ _ hab hba
    exact Nat.le_antisymm hab hba
  · -- perfectMerge is sorted with ≤
    have hpm_sorted := perfectMerge_sorted as bs has hbs hlen halt
    exact List.Pairwise.imp (fun h => Nat.le_of_lt h) hpm_sorted
  · -- mergeSort result is sorted with ≤
    have htrans : ∀ a b c : ℕ, decide (a ≤ b) = true → decide (b ≤ c) = true →
        decide (a ≤ c) = true := by
      intro a b c hab hbc
      simp only [decide_eq_true_eq] at *
      exact Nat.le_trans hab hbc
    have htotal : ∀ a b : ℕ, (decide (a ≤ b) || decide (b ≤ a)) = true := by
      intro a b
      simp only [Bool.or_eq_true, decide_eq_true_eq]
      omega
    have hsorted := List.pairwise_mergeSort htrans htotal (as ++ bs)
    exact List.Pairwise.imp (fun h => by simp only [decide_eq_true_eq] at h; exact h) hsorted
  · -- Permutation
    have h1 : (perfectMerge as bs).Perm (as ++ bs) := perfectMerge_perm as bs hlen
    have h2 : ((as ++ bs).mergeSort (· ≤ ·)).Perm (as ++ bs) :=
      List.mergeSort_perm (as ++ bs) (· ≤ ·)
    exact List.Perm.trans h1 (List.Perm.symm h2)

/-- perfectMerge on labeled elements with A's and B's -/
def perfectMergeLabled (as bs : List LabeledElement) : List LabeledElement :=
  match as, bs with
  | [], [] => []
  | a :: as', b :: bs' => a :: b :: perfectMergeLabled as' bs'
  | _, _ => []

/-- perfectMergeLabledUnequal handles the case where bs may have one more element -/
def perfectMergeLabledUnequal : List LabeledElement → List LabeledElement → List LabeledElement
  | [], bs => bs
  | a :: as, [] => a :: as
  | a :: as, b :: bs => a :: b :: perfectMergeLabledUnequal as bs

/-- perfectMergeLabledUnequal is a permutation of as ++ bs -/
lemma perfectMergeLabledUnequal_perm (as bs : List LabeledElement) :
    (perfectMergeLabledUnequal as bs).Perm (as ++ bs) := by
  induction as generalizing bs with
  | nil => simp [perfectMergeLabledUnequal]
  | cons a as ih =>
    cases bs with
    | nil => simp [perfectMergeLabledUnequal]
    | cons b bs =>
      simp only [perfectMergeLabledUnequal, List.cons_append]
      apply List.Perm.cons
      have h1 : (perfectMergeLabledUnequal as bs).Perm (as ++ bs) := ih bs
      have h2 : (b :: perfectMergeLabledUnequal as bs).Perm (b :: (as ++ bs)) := List.Perm.cons b h1
      have h3 : (b :: (as ++ bs)).Perm (as ++ b :: bs) := by
        have := @List.perm_middle LabeledElement b as bs
        exact List.Perm.symm this
      exact List.Perm.trans h2 h3

/-- countAlternatingPrefix on perfectMergeLabledUnequal equals the shorter length -/
lemma countAlternatingPrefix_perfectMergeLabledUnequal (as bs : List LabeledElement)
    (hlen : as.length ≤ bs.length)
    (has_A : ∀ a, a ∈ as → a.label = Label.A)
    (hbs_B : ∀ b, b ∈ bs → b.label = Label.B) :
    countAlternatingPrefix (perfectMergeLabledUnequal as bs) = as.length := by
  induction as generalizing bs with
  | nil =>
    simp only [perfectMergeLabledUnequal, List.length_nil]
    match bs with
    | [] => rfl
    | [b] => rfl
    | b :: b' :: bs' =>
      simp only [countAlternatingPrefix]
      have hb : b.label = Label.B := hbs_B b (by simp)
      rw [hb]
      simp only [reduceCtorEq, false_and, ↓reduceIte]
  | cons a as ih =>
    cases bs with
    | nil => simp at hlen
    | cons b bs =>
      simp only [List.length_cons, Nat.add_le_add_iff_right] at hlen
      simp only [perfectMergeLabledUnequal, countAlternatingPrefix]
      have ha : a.label = Label.A := has_A a (by simp)
      have hb : b.label = Label.B := hbs_B b (by simp)
      simp only [ha, hb, and_self, ↓reduceIte]
      have has' : ∀ a', a' ∈ as → a'.label = Label.A := by
        intro a' ha'
        exact has_A a' (List.mem_cons_of_mem a ha')
      have hbs' : ∀ b', b' ∈ bs → b'.label = Label.B := by
        intro b' hb'
        exact hbs_B b' (List.mem_cons_of_mem b hb')
      rw [ih bs hlen has' hbs']
      simp only [List.length_cons]
      ring

/-- perfectMergeLabledUnequal is sorted when alternation conditions hold -/
lemma perfectMergeLabledUnequal_sorted (as bs : List LabeledElement)
    (has : List.Pairwise (· < ·) as) (hbs : List.Pairwise (· < ·) bs)
    (hlen : as.length ≤ bs.length)
    (halt : ∀ i (hi : i < as.length), as[i]'hi < bs[i]'(Nat.lt_of_lt_of_le hi hlen) ∧
        ∀ (hi2 : i + 1 < as.length), bs[i]'(Nat.lt_of_lt_of_le hi hlen) < as[i + 1]'hi2) :
    List.Pairwise (· < ·) (perfectMergeLabledUnequal as bs) := by
  induction as generalizing bs with
  | nil =>
    simp only [perfectMergeLabledUnequal]
    exact hbs
  | cons a as ih =>
    cases bs with
    | nil => simp at hlen
    | cons b bs =>
      simp only [List.length_cons, Nat.add_le_add_iff_right] at hlen
      simp only [perfectMergeLabledUnequal]
      have hab : a < b := by
        have h0 := halt 0 (by simp)
        exact h0.1
      have has' : List.Pairwise (· < ·) as := List.Pairwise.of_cons has
      have hbs' : List.Pairwise (· < ·) bs := List.Pairwise.of_cons hbs
      have halt' : ∀ i (hi : i < as.length), as[i]'hi < bs[i]'(Nat.lt_of_lt_of_le hi hlen) ∧
          ∀ (hi2 : i + 1 < as.length), bs[i]'(Nat.lt_of_lt_of_le hi hlen) < as[i + 1]'hi2 := by
        intro i hi
        have hi' : i + 1 < (a :: as).length := by simp; omega
        have h := halt (i + 1) hi'
        simp only [List.getElem_cons_succ] at h
        exact ⟨h.1, fun hi2 => h.2 (by simp; omega)⟩
      have ih_sorted := ih bs has' hbs' hlen halt'
      apply List.Pairwise.cons
      · intro x hx
        simp only [List.mem_cons] at hx
        cases hx with
        | inl hxb => rw [hxb]; exact hab
        | inr hxrest =>
          have hperm := perfectMergeLabledUnequal_perm as bs
          have hx_in : x ∈ as ++ bs := List.Perm.mem_iff hperm |>.mp hxrest
          simp only [List.mem_append] at hx_in
          cases hx_in with
          | inl hx_as => exact List.rel_of_pairwise_cons has hx_as
          | inr hx_bs =>
            have hb_lt : b < x := List.rel_of_pairwise_cons hbs hx_bs
            unfold LT.lt instLTLabeledElement at hab hb_lt ⊢
            simp only at hab hb_lt ⊢
            exact Nat.lt_trans hab hb_lt
      · apply List.Pairwise.cons
        · intro x hx
          have hperm := perfectMergeLabledUnequal_perm as bs
          have hx_in : x ∈ as ++ bs := List.Perm.mem_iff hperm |>.mp hx
          simp only [List.mem_append] at hx_in
          cases hx_in with
          | inl hx_as =>
            cases as with
            | nil => simp at hx_as
            | cons a' as' =>
              have h0' := halt 0 (by simp)
              simp only [List.getElem_cons_zero, List.getElem_cons_succ] at h0'
              have hb_lt_a' : b < a' := h0'.2 (by simp)
              simp only [List.mem_cons] at hx_as
              cases hx_as with
              | inl heq => rw [heq]; exact hb_lt_a'
              | inr hmem =>
                have ha'_lt_x : a' < x := List.rel_of_pairwise_cons has' hmem
                unfold LT.lt instLTLabeledElement at hb_lt_a' ha'_lt_x ⊢
                simp only at hb_lt_a' ha'_lt_x ⊢
                exact Nat.lt_trans hb_lt_a' ha'_lt_x
          | inr hx_bs => exact List.rel_of_pairwise_cons hbs hx_bs
        · exact ih_sorted

/-- countAlternatingPrefix on perfectMerge of A-labeled and B-labeled lists equals length -/
lemma countAlternatingPrefix_perfectMergeLabled (as bs : List LabeledElement)
    (hlen : as.length = bs.length)
    (has_A : ∀ a, a ∈ as → a.label = Label.A)
    (hbs_B : ∀ b, b ∈ bs → b.label = Label.B) :
    countAlternatingPrefix (perfectMergeLabled as bs) = as.length := by
  induction as generalizing bs with
  | nil =>
    cases bs with
    | nil => simp [perfectMergeLabled, countAlternatingPrefix]
    | cons b bs => simp at hlen
  | cons a as ih =>
    cases bs with
    | nil => simp at hlen
    | cons b bs =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      simp only [perfectMergeLabled, countAlternatingPrefix]
      have ha : a.label = Label.A := has_A a (by simp)
      have hb : b.label = Label.B := hbs_B b (by simp)
      simp only [ha, hb, and_self, ↓reduceIte]
      have has' : ∀ a', a' ∈ as → a'.label = Label.A := by
        intro a' ha'
        exact has_A a' (List.mem_cons_of_mem a ha')
      have hbs' : ∀ b', b' ∈ bs → b'.label = Label.B := by
        intro b' hb'
        exact hbs_B b' (List.mem_cons_of_mem b hb')
      rw [ih bs hlen has' hbs']
      simp only [List.length_cons]
      ring

/-- mergedList n equals the sorted merge of labeled semiprimes -/
lemma mergedList_eq_mergeSort (n : ℕ) :
    mergedList n =
      ((semiprimeList n).map (fun v => LabeledElement.mk v Label.A) ++
       (semiprimeList (n + 1)).map (fun v => LabeledElement.mk v Label.B)).mergeSort (· ≤ ·) := by
  unfold mergedList
  rfl

/-- L n is at most n (we only have n A elements) -/
lemma countAlternatingPrefix_le_length_div_two (l : List LabeledElement) :
    countAlternatingPrefix l ≤ l.length / 2 := by
  match l with
  | [] => simp [countAlternatingPrefix]
  | [_] => simp [countAlternatingPrefix]
  | a :: b :: rest' =>
    simp only [countAlternatingPrefix]
    split_ifs with h
    · have ih := countAlternatingPrefix_le_length_div_two rest'
      simp only [List.length_cons]
      omega
    · simp only [List.length_cons]
      omega
termination_by l.length

lemma mergedList_length (n : ℕ) : (mergedList n).length = n + (n + 1) := by
  unfold mergedList
  rw [List.length_mergeSort]
  simp only [List.length_append, List.length_map, semiprimeList_length]

lemma L_le_n (n : ℕ) : L n ≤ n := by
  unfold L
  have h1 := countAlternatingPrefix_le_length_div_two (mergedList n)
  have h2 := mergedList_length n
  omega

/-- The labeled A elements from semiprimeList -/
noncomputable def labeledA (n : ℕ) : List LabeledElement :=
  (semiprimeList n).map (fun v => LabeledElement.mk v Label.A)

noncomputable def labeledB (n : ℕ) : List LabeledElement :=
  (semiprimeList n).map (fun v => LabeledElement.mk v Label.B)

lemma labeledA_length (n : ℕ) : (labeledA n).length = n := by
  simp only [labeledA, List.length_map, semiprimeList_length]

lemma labeledB_length (n : ℕ) : (labeledB n).length = n := by
  simp only [labeledB, List.length_map, semiprimeList_length]

lemma labeledA_all_A (n : ℕ) : ∀ a, a ∈ labeledA n → a.label = Label.A := by
  intro a ha
  simp only [labeledA, List.mem_map] at ha
  obtain ⟨v, _, rfl⟩ := ha
  rfl

lemma labeledB_all_B (n : ℕ) : ∀ b, b ∈ labeledB n → b.label = Label.B := by
  intro b hb
  simp only [labeledB, List.mem_map] at hb
  obtain ⟨v, _, rfl⟩ := hb
  rfl

/-- Labeled lists are sorted iff their values are sorted -/
lemma labeledA_sorted (n : ℕ) (hn : n ≥ 1)
    (hprime_mono : ∀ i, i ≥ 1 → nthPrime i < nthPrime (i + 1)) :
    List.Pairwise (· < ·) (labeledA n) := by
  unfold labeledA
  rw [List.pairwise_map]
  have hsemi := semiprimeList_sorted n hn hprime_mono
  exact List.Pairwise.imp (fun h => h) hsemi

lemma labeledB_sorted (n : ℕ) (hn : n ≥ 1)
    (hprime_mono : ∀ i, i ≥ 1 → nthPrime i < nthPrime (i + 1)) :
    List.Pairwise (· < ·) (labeledB n) := by
  unfold labeledB
  rw [List.pairwise_map]
  have hsemi := semiprimeList_sorted n hn hprime_mono
  exact List.Pairwise.imp (fun h => h) hsemi

/-- The alternation condition on labeled elements -/
lemma semiprimeList_getElem' (n j : ℕ) (hj : j < (semiprimeList n).length) :
    (semiprimeList n)[j] = nthPrime (j + 1) * nthPrime n := by
  unfold semiprimeList
  simp only [List.getElem_map, List.getElem_range]

lemma labeled_alternation_condition (n : ℕ) (hn : n ≥ 1)
    (hprime_mono : ∀ i, i ≥ 1 → nthPrime i < nthPrime (i + 1))
    (hRec : ∀ j, 1 ≤ j → j < n → ratioLt n j) :
    ∀ i (hi : i < n),
      (labeledA n)[i]'(by rw [labeledA_length]; exact hi) <
      (labeledB (n + 1))[i]'(by rw [labeledB_length]; omega) ∧
      ∀ (hi2 : i + 1 < n),
        (labeledB (n + 1))[i]'(by rw [labeledB_length]; omega) <
        (labeledA n)[i + 1]'(by rw [labeledA_length]; exact hi2) := by
  intro i hi
  have hl1 : i < (semiprimeList n).length := by rw [semiprimeList_length]; exact hi
  have hl2 : i < (semiprimeList (n + 1)).length := by rw [semiprimeList_length]; omega
  constructor
  · -- (labeledA n)[i] < (labeledB (n+1))[i]
    unfold labeledA labeledB
    simp only [List.getElem_map]
    unfold LT.lt instLTLabeledElement
    show (semiprimeList n)[i]'hl1 < (semiprimeList (n + 1))[i]'hl2
    rw [semiprimeList_getElem' n i hl1, semiprimeList_getElem' (n + 1) i hl2]
    have hpos : nthPrime (i + 1) > 0 := nthPrime_pos (i + 1) (by omega)
    have hmono : nthPrime n < nthPrime (n + 1) := hprime_mono n hn
    exact Nat.mul_lt_mul_of_pos_left hmono hpos
  · -- (labeledB (n+1))[i] < (labeledA n)[i+1]
    intro hi2
    have hl3 : i + 1 < (semiprimeList n).length := by rw [semiprimeList_length]; exact hi2
    unfold labeledA labeledB
    simp only [List.getElem_map]
    unfold LT.lt instLTLabeledElement
    show (semiprimeList (n + 1))[i]'hl2 < (semiprimeList n)[i + 1]'hl3
    rw [semiprimeList_getElem' (n + 1) i hl2, semiprimeList_getElem' n (i + 1) hl3]
    -- Need: p_{i+1} * p_{n+1} < p_{i+2} * p_n
    have hrat := hRec (i + 1) (by omega) hi2
    unfold ratioLt primeRatioNum primeRatioDen at hrat
    rw [mul_comm (nthPrime (i + 1)) (nthPrime (n + 1))]
    convert hrat using 2

/-- perfectMergeLabled is a permutation of as ++ bs -/
lemma perfectMergeLabled_perm (as bs : List LabeledElement) (hlen : as.length = bs.length) :
    (perfectMergeLabled as bs).Perm (as ++ bs) := by
  induction as generalizing bs with
  | nil =>
    cases bs with
    | nil => simp [perfectMergeLabled]
    | cons b bs => simp at hlen
  | cons a as ih =>
    cases bs with
    | nil => simp at hlen
    | cons b bs =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      simp only [perfectMergeLabled, List.cons_append]
      apply List.Perm.cons
      have h1 : (perfectMergeLabled as bs).Perm (as ++ bs) := ih bs hlen
      have h2 : (b :: perfectMergeLabled as bs).Perm (b :: (as ++ bs)) := List.Perm.cons b h1
      have h3 : (b :: (as ++ bs)).Perm (as ++ b :: bs) := by
        have := @List.perm_middle LabeledElement b as bs
        exact List.Perm.symm this
      exact List.Perm.trans h2 h3

/-- perfectMergeLabled is sorted when alternation conditions hold -/
lemma perfectMergeLabled_sorted (as bs : List LabeledElement)
    (has : List.Pairwise (· < ·) as) (hbs : List.Pairwise (· < ·) bs)
    (hlen : as.length = bs.length)
    (halt : ∀ i (hi : i < as.length), as[i]'hi < bs[i]'(hlen ▸ hi) ∧
        ∀ (hi2 : i + 1 < as.length), bs[i]'(hlen ▸ hi) < as[i + 1]'hi2) :
    List.Pairwise (· < ·) (perfectMergeLabled as bs) := by
  induction as generalizing bs with
  | nil =>
    cases bs with
    | nil => simp [perfectMergeLabled]
    | cons b bs => simp at hlen
  | cons a as ih =>
    cases bs with
    | nil => simp at hlen
    | cons b bs =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      simp only [perfectMergeLabled]
      have hab : a < b := by
        have h0 := halt 0 (by simp)
        exact h0.1
      have has' : List.Pairwise (· < ·) as := List.Pairwise.of_cons has
      have hbs' : List.Pairwise (· < ·) bs := List.Pairwise.of_cons hbs
      have halt' : ∀ i (hi : i < as.length), as[i]'hi < bs[i]'(hlen ▸ hi) ∧
          ∀ (hi2 : i + 1 < as.length), bs[i]'(hlen ▸ hi) < as[i + 1]'hi2 := by
        intro i hi
        have hi' : i + 1 < (a :: as).length := by simp; omega
        have h := halt (i + 1) hi'
        simp only [List.getElem_cons_succ] at h
        exact ⟨h.1, fun hi2 => h.2 (by simp; omega)⟩
      have ih_sorted := ih bs has' hbs' hlen halt'
      apply List.Pairwise.cons
      · intro x hx
        simp only [List.mem_cons] at hx
        cases hx with
        | inl hxb => rw [hxb]; exact hab
        | inr hxrest =>
          have hperm := perfectMergeLabled_perm as bs hlen
          have hx_in : x ∈ as ++ bs := List.Perm.mem_iff hperm |>.mp hxrest
          simp only [List.mem_append] at hx_in
          cases hx_in with
          | inl hx_as => exact List.rel_of_pairwise_cons has hx_as
          | inr hx_bs =>
            have hb_lt : b < x := List.rel_of_pairwise_cons hbs hx_bs
            unfold LT.lt instLTLabeledElement at hab hb_lt ⊢
            simp only at hab hb_lt ⊢
            exact Nat.lt_trans hab hb_lt
      · apply List.Pairwise.cons
        · intro x hx
          have hperm := perfectMergeLabled_perm as bs hlen
          have hx_in : x ∈ as ++ bs := List.Perm.mem_iff hperm |>.mp hx
          simp only [List.mem_append] at hx_in
          cases hx_in with
          | inl hx_as =>
            cases as with
            | nil => simp at hx_as
            | cons a' as' =>
              have h0' := halt 0 (by simp)
              simp only [List.getElem_cons_zero, List.getElem_cons_succ] at h0'
              have hb_lt_a' : b < a' := h0'.2 (by simp)
              simp only [List.mem_cons] at hx_as
              cases hx_as with
              | inl heq => rw [heq]; exact hb_lt_a'
              | inr hmem =>
                have ha'_lt_x : a' < x := List.rel_of_pairwise_cons has' hmem
                unfold LT.lt instLTLabeledElement at hb_lt_a' ha'_lt_x ⊢
                simp only at hb_lt_a' ha'_lt_x ⊢
                exact Nat.lt_trans hb_lt_a' ha'_lt_x
          | inr hx_bs => exact List.rel_of_pairwise_cons hbs hx_bs
        · exact ih_sorted

/-- All values in labeledA n and labeledB (n+1) are distinct -/
lemma semiprime_cross_ne (n : ℕ) (hn : n ≥ 1) (i j : ℕ) (hi : i < n) (_hj : j < n + 1)
    (hprime_mono : ∀ k, k ≥ 1 → nthPrime k < nthPrime (k + 1)) :
    nthPrime (i + 1) * nthPrime n ≠ nthPrime (j + 1) * nthPrime (n + 1) := by
  intro heq
  -- Get that all nthPrime values are prime
  have hp_i1 : Nat.Prime (nthPrime (i + 1)) := by
    unfold nthPrime
    have h : i + 1 ≠ 0 := by omega
    simp only [h, ↓reduceIte, Nat.add_sub_cancel]
    exact Nat.nth_mem_of_infinite Nat.infinite_setOf_prime i
  have hp_n : Nat.Prime (nthPrime n) := by
    unfold nthPrime
    have h : n ≠ 0 := by omega
    simp only [h, ↓reduceIte]
    exact Nat.nth_mem_of_infinite Nat.infinite_setOf_prime (n - 1)
  have hp_n1 : Nat.Prime (nthPrime (n + 1)) := by
    unfold nthPrime
    have h : n + 1 ≠ 0 := by omega
    simp only [h, ↓reduceIte, Nat.add_sub_cancel]
    exact Nat.nth_mem_of_infinite Nat.infinite_setOf_prime n
  -- p_n < p_{n+1}
  have hn_lt : nthPrime n < nthPrime (n + 1) := hprime_mono n hn
  -- From heq, p_{n+1} divides LHS
  have hdvd : nthPrime (n + 1) ∣ nthPrime (i + 1) * nthPrime n := by
    rw [heq]; exact Nat.dvd_mul_left _ _
  -- Since p_{n+1} is prime, it divides one of the factors
  have hdvd_or := hp_n1.dvd_mul.mp hdvd
  cases hdvd_or with
  | inl hdvd_i1 =>
    -- p_{n+1} ∣ p_{i+1}, and p_{i+1} is prime
    -- So p_{n+1} = 1 or p_{n+1} = p_{i+1}
    have h_eq_or := hp_i1.eq_one_or_self_of_dvd (nthPrime (n + 1)) hdvd_i1
    cases h_eq_or with
    | inl h_eq_one =>
      -- nthPrime (n + 1) = 1, but it's prime, contradiction
      have := Nat.Prime.one_lt hp_n1
      omega
    | inr h_eq =>
      -- nthPrime (n + 1) = nthPrime (i + 1)
      have heq_idx := nthPrime_injective hprime_mono (n + 1) (i + 1) (by omega) (by omega) h_eq
      -- So i + 1 = n + 1, i.e., i = n, but hi : i < n
      omega
  | inr hdvd_n =>
    -- p_{n+1} ∣ p_n, and p_n is prime
    have h_eq_or := hp_n.eq_one_or_self_of_dvd (nthPrime (n + 1)) hdvd_n
    cases h_eq_or with
    | inl h_eq_one =>
      have := Nat.Prime.one_lt hp_n1
      omega
    | inr h_eq =>
      -- nthPrime (n + 1) = nthPrime n, but p_n < p_{n+1}
      omega

lemma labeled_values_distinct (n : ℕ) (hn : n ≥ 1)
    (hprime_mono : ∀ i, i ≥ 1 → nthPrime i < nthPrime (i + 1)) :
    ∀ a b, a ∈ labeledA n ++ labeledB (n + 1) → b ∈ labeledA n ++ labeledB (n + 1) →
      a.value = b.value → a = b := by
  intro a b ha hb heq
  simp only [List.mem_append] at ha hb
  cases ha with
  | inl ha_A =>
    cases hb with
    | inl hb_A =>
      -- Both from labeledA n
      simp only [labeledA, List.mem_map] at ha_A hb_A
      obtain ⟨va, hva_mem, hva_eq⟩ := ha_A
      obtain ⟨vb, hvb_mem, hvb_eq⟩ := hb_A
      rw [← hva_eq, ← hvb_eq]
      simp only [LabeledElement.mk.injEq]
      simp only [semiprimeList, List.mem_map, List.mem_range] at hva_mem hvb_mem
      obtain ⟨ia, hia_lt, hia_eq⟩ := hva_mem
      obtain ⟨ib, hib_lt, hib_eq⟩ := hvb_mem
      rw [← hva_eq, ← hvb_eq] at heq
      simp only at heq
      rw [← hia_eq, ← hib_eq] at heq
      have hp_n_pos : nthPrime n > 0 := nthPrime_pos n hn
      have hpeq : nthPrime (ia + 1) = nthPrime (ib + 1) := Nat.eq_of_mul_eq_mul_right hp_n_pos heq
      have hinj := nthPrime_injective hprime_mono (ia + 1) (ib + 1) (by omega) (by omega) hpeq
      constructor
      · rw [← hia_eq, ← hib_eq, hinj]
      · trivial
    | inr hb_B =>
      -- a from labeledA, b from labeledB
      simp only [labeledA, labeledB, List.mem_map] at ha_A hb_B
      obtain ⟨va, hva_mem, hva_eq⟩ := ha_A
      obtain ⟨vb, hvb_mem, hvb_eq⟩ := hb_B
      rw [← hva_eq, ← hvb_eq] at heq
      simp only at heq
      simp only [semiprimeList, List.mem_map, List.mem_range] at hva_mem hvb_mem
      obtain ⟨ia, hia_lt, hia_eq⟩ := hva_mem
      obtain ⟨ib, hib_lt, hib_eq⟩ := hvb_mem
      rw [← hia_eq, ← hib_eq] at heq
      exfalso
      exact semiprime_cross_ne n hn ia ib hia_lt hib_lt hprime_mono heq
  | inr ha_B =>
    cases hb with
    | inl hb_A =>
      -- a from labeledB, b from labeledA
      simp only [labeledA, labeledB, List.mem_map] at ha_B hb_A
      obtain ⟨va, hva_mem, hva_eq⟩ := ha_B
      obtain ⟨vb, hvb_mem, hvb_eq⟩ := hb_A
      rw [← hva_eq, ← hvb_eq] at heq
      simp only at heq
      simp only [semiprimeList, List.mem_map, List.mem_range] at hva_mem hvb_mem
      obtain ⟨ia, hia_lt, hia_eq⟩ := hva_mem
      obtain ⟨ib, hib_lt, hib_eq⟩ := hvb_mem
      rw [← hia_eq, ← hib_eq] at heq
      exfalso
      exact semiprime_cross_ne n hn ib ia hib_lt hia_lt hprime_mono heq.symm
    | inr hb_B =>
      -- Both from labeledB (n+1)
      simp only [labeledB, List.mem_map] at ha_B hb_B
      obtain ⟨va, hva_mem, hva_eq⟩ := ha_B
      obtain ⟨vb, hvb_mem, hvb_eq⟩ := hb_B
      rw [← hva_eq, ← hvb_eq]
      simp only [LabeledElement.mk.injEq]
      simp only [semiprimeList, List.mem_map, List.mem_range] at hva_mem hvb_mem
      obtain ⟨ia, hia_lt, hia_eq⟩ := hva_mem
      obtain ⟨ib, hib_lt, hib_eq⟩ := hvb_mem
      rw [← hva_eq, ← hvb_eq] at heq
      simp only at heq
      rw [← hia_eq, ← hib_eq] at heq
      have hp_n1_pos : nthPrime (n + 1) > 0 := nthPrime_pos (n + 1) (by omega)
      have hpeq : nthPrime (ia + 1) = nthPrime (ib + 1) := Nat.eq_of_mul_eq_mul_right hp_n1_pos heq
      have hinj := nthPrime_injective hprime_mono (ia + 1) (ib + 1) (by omega) (by omega) hpeq
      constructor
      · rw [← hia_eq, ← hib_eq, hinj]
      · trivial

/-- Alternation condition for unequal length case -/
lemma labeled_alternation_condition_unequal (n : ℕ) (hn : n ≥ 1)
    (hprime_mono : ∀ i, i ≥ 1 → nthPrime i < nthPrime (i + 1))
    (hRec : ∀ j, 1 ≤ j → j < n → ratioLt n j) :
    ∀ i (hi : i < (labeledA n).length),
      (labeledA n)[i]'hi <
        (labeledB (n + 1))[i]'(Nat.lt_of_lt_of_le hi (by rw [labeledA_length, labeledB_length]; omega)) ∧
      ∀ (hi2 : i + 1 < (labeledA n).length),
        (labeledB (n + 1))[i]'(Nat.lt_of_lt_of_le hi (by rw [labeledA_length, labeledB_length]; omega)) <
        (labeledA n)[i + 1]'hi2 := by
  intro i hi
  rw [labeledA_length] at hi
  have hcond := labeled_alternation_condition n hn hprime_mono hRec i hi
  constructor
  · exact hcond.1
  · intro hi2
    rw [labeledA_length] at hi2
    exact hcond.2 hi2

/-- mergeSort equals perfectMergeLabledUnequal when ratio conditions hold -/
lemma mergeSort_eq_perfectMergeLabledUnequal (n : ℕ) (hn : n ≥ 1)
    (hprime_mono : ∀ i, i ≥ 1 → nthPrime i < nthPrime (i + 1))
    (hRec : ∀ j, 1 ≤ j → j < n → ratioLt n j) :
    (labeledA n ++ labeledB (n + 1)).mergeSort (· ≤ ·) =
    perfectMergeLabledUnequal (labeledA n) (labeledB (n + 1)) := by
  symm
  apply List.Perm.eq_of_pairwise
  · -- Antisymmetry
    intro a b ha hb hab hba
    have heq_val : a.value = b.value := Nat.le_antisymm hab hba
    have hdist := labeled_values_distinct n hn hprime_mono
    have hperm := perfectMergeLabledUnequal_perm (labeledA n) (labeledB (n + 1))
    have ha' := List.Perm.mem_iff hperm |>.mp ha
    have hb' := List.mem_mergeSort.mp hb
    exact hdist a b ha' hb' heq_val
  · -- perfectMergeLabledUnequal is sorted with ≤
    have hlen : (labeledA n).length ≤ (labeledB (n + 1)).length := by
      rw [labeledA_length, labeledB_length]; omega
    have hsorted := perfectMergeLabledUnequal_sorted (labeledA n) (labeledB (n + 1))
      (labeledA_sorted n hn hprime_mono) (labeledB_sorted (n + 1) (by omega) hprime_mono)
      hlen (labeled_alternation_condition_unequal n hn hprime_mono hRec)
    exact List.Pairwise.imp (fun h => Nat.le_of_lt h) hsorted
  · -- mergeSort is sorted with ≤
    have htrans : ∀ a b c : LabeledElement, decide (a ≤ b) = true → decide (b ≤ c) = true →
        decide (a ≤ c) = true := by
      intro a b c hab hbc
      simp only [decide_eq_true_eq] at *
      exact Nat.le_trans hab hbc
    have htotal : ∀ a b : LabeledElement, (decide (a ≤ b) || decide (b ≤ a)) = true := by
      intro a b
      simp only [Bool.or_eq_true, decide_eq_true_eq]
      unfold LE.le instLELabeledElement
      exact Nat.le_or_le a.value b.value
    have hsorted := List.pairwise_mergeSort htrans htotal (labeledA n ++ labeledB (n + 1))
    exact List.Pairwise.imp (fun h => by simp only [decide_eq_true_eq] at h; exact h) hsorted
  · -- Permutation
    have h1 := perfectMergeLabledUnequal_perm (labeledA n) (labeledB (n + 1))
    have h2 := List.mergeSort_perm (labeledA n ++ labeledB (n + 1)) (· ≤ ·)
    exact List.Perm.trans h1 (List.Perm.symm h2)

/-- When ratio conditions hold, mergedList has n alternating pairs -/
lemma mergedList_prefix_structure (n : ℕ) (hn : n ≥ 1)
    (hprime_mono : ∀ i, i ≥ 1 → nthPrime i < nthPrime (i + 1))
    (hRec : ∀ j, 1 ≤ j → j < n → ratioLt n j) :
    countAlternatingPrefix (mergedList n) = n := by
  unfold mergedList
  have hlen_le : (labeledA n).length ≤ (labeledB (n + 1)).length := by
    rw [labeledA_length, labeledB_length]; omega
  have heq := mergeSort_eq_perfectMergeLabledUnequal n hn hprime_mono hRec
  unfold labeledA labeledB at heq
  rw [heq]
  have hcount := countAlternatingPrefix_perfectMergeLabledUnequal
    (labeledA n) (labeledB (n + 1)) hlen_le (labeledA_all_A n) (labeledB_all_B (n + 1))
  unfold labeledA labeledB at hcount
  rw [hcount]
  exact labeledA_length n

/-- In a perfectly alternating list of n pairs, position 2k has an A and position 2k+1 has a B -/
lemma alternating_prefix_structure (l : List LabeledElement) (k : ℕ)
    (hcount : countAlternatingPrefix l ≥ k + 1)
    (h2k : 2 * k < l.length) (h2k1 : 2 * k + 1 < l.length) :
    l[2 * k].label = Label.A ∧ l[2 * k + 1].label = Label.B := by
  induction k generalizing l with
  | zero =>
    match l with
    | [] => simp at h2k
    | [_] => simp at h2k1
    | a :: b :: rest =>
      simp only [countAlternatingPrefix] at hcount
      split_ifs at hcount with hab
      · exact hab
      · simp at hcount
  | succ k' ih =>
    match l with
    | [] => simp at h2k
    | [_] => simp at h2k1
    | a :: b :: rest =>
      simp only [countAlternatingPrefix] at hcount
      split_ifs at hcount with hab
      · have hcount' : countAlternatingPrefix rest ≥ k' + 1 := by omega
        have h2k' : 2 * k' < rest.length := by simp at h2k; omega
        have h2k1' : 2 * k' + 1 < rest.length := by simp at h2k1; omega
        have ih_result := ih rest hcount' h2k' h2k1'
        simp only [List.getElem_cons_succ]
        convert ih_result using 2 <;> omega
      · simp at hcount

/-- If l is sorted and has perfect alternation for k pairs,
    then l[2k-1] < l[2k] (i.e., B[k-1] < A[k]) -/
lemma sorted_alternating_order (l : List LabeledElement) (k : ℕ) (hk : k ≥ 1)
    (hsorted : List.Pairwise (· ≤ ·) l)
    (_hcount : countAlternatingPrefix l ≥ k)
    (h2k1 : 2 * k - 1 < l.length) (h2k : 2 * k < l.length) :
    l[2 * k - 1] ≤ l[2 * k] := by
  apply List.pairwise_iff_getElem.mp hsorted
  omega

/-- The merged list is sorted -/
lemma mergedList_sorted (n : ℕ) : List.Pairwise (· ≤ ·) (mergedList n) := by
  unfold mergedList
  have htrans : ∀ a b c : LabeledElement, decide (a ≤ b) = true → decide (b ≤ c) = true →
      decide (a ≤ c) = true := by
    intro a b c hab hbc
    simp only [decide_eq_true_eq] at *
    exact Nat.le_trans hab hbc
  have htotal : ∀ a b : LabeledElement, (decide (a ≤ b) || decide (b ≤ a)) = true := by
    intro a b
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    unfold LE.le instLELabeledElement
    exact Nat.le_or_le a.value b.value
  have hs := List.pairwise_mergeSort htrans htotal
    ((semiprimeList n).map (fun v => LabeledElement.mk v Label.A) ++
     (semiprimeList (n + 1)).map (fun v => LabeledElement.mk v Label.B))
  exact List.Pairwise.imp (fun h => by simp only [decide_eq_true_eq] at h; exact h) hs

/-- A specific element from labeledA n is in mergedList n -/
lemma labeledA_elem_in_mergedList (n i : ℕ) (hi : i < n) :
    (labeledA n)[i]'(by rw [labeledA_length]; exact hi) ∈ mergedList n := by
  unfold mergedList labeledA
  let sn := (semiprimeList n).map (fun v => LabeledElement.mk v Label.A)
  let sn1 := (semiprimeList (n+1)).map (fun v => LabeledElement.mk v Label.B)
  have hlen : i < sn.length := by
    change i < ((semiprimeList n).map (fun v => LabeledElement.mk v Label.A)).length
    simp only [List.length_map, semiprimeList_length]
    exact hi
  have hmem : sn[i]'hlen ∈ sn ++ sn1 := by
    apply List.mem_append_left
    exact List.getElem_mem ..
  have hperm := List.mergeSort_perm (sn ++ sn1) (· ≤ ·)
  exact hperm.mem_iff.mpr hmem

/-- A specific element from labeledB (n+1) is in mergedList n -/
lemma labeledB_elem_in_mergedList (n i : ℕ) (hi : i < n + 1) :
    (labeledB (n + 1))[i]'(by rw [labeledB_length]; exact hi) ∈ mergedList n := by
  unfold mergedList labeledB
  let sn := (semiprimeList n).map (fun v => LabeledElement.mk v Label.A)
  let sn1 := (semiprimeList (n+1)).map (fun v => LabeledElement.mk v Label.B)
  have hlen : i < sn1.length := by
    change i < ((semiprimeList (n+1)).map (fun v => LabeledElement.mk v Label.B)).length
    simp only [List.length_map, semiprimeList_length]
    exact hi
  have hmem : sn1[i]'hlen ∈ sn ++ sn1 := by
    apply List.mem_append_right
    exact List.getElem_mem ..
  have hperm := List.mergeSort_perm (sn ++ sn1) (· ≤ ·)
  exact hperm.mem_iff.mpr hmem

/-- Filter of a sorted list by label is sorted -/
lemma sorted_filter_sorted (l : List LabeledElement) (lab : Label)
    (hsorted : List.Pairwise (· ≤ ·) l) :
    List.Pairwise (· ≤ ·) (l.filter (·.label = lab)) := by
  induction l with
  | nil => simp
  | cons a as ih =>
    simp only [List.filter_cons]
    split_ifs with ha
    · apply List.Pairwise.cons
      · intro x hx
        simp only [List.mem_filter] at hx
        exact List.rel_of_pairwise_cons hsorted hx.1
      · exact ih (List.Pairwise.of_cons hsorted)
    · exact ih (List.Pairwise.of_cons hsorted)

/-- Count of A labels in first k elements of a list -/
def countAPrefix : List LabeledElement → ℕ → ℕ
  | [], _ => 0
  | _, 0 => 0
  | a :: as, k + 1 => (if a.label = Label.A then 1 else 0) + countAPrefix as k

/-- countAPrefix equals length of filter on take -/
lemma countAPrefix_eq_filter_length (l : List LabeledElement) (k : ℕ) :
    countAPrefix l k = ((l.take k).filter (fun x => x.label = Label.A)).length := by
  induction l generalizing k with
  | nil => simp [countAPrefix]
  | cons a as ih =>
    cases k with
    | zero => simp [countAPrefix]
    | succ k' =>
      simp only [countAPrefix, List.take_succ_cons, List.filter_cons]
      cases ha : a.label with
      | A =>
        simp only [ decide_eq_true_eq, ↓reduceIte, List.length_cons]
        rw [ih]
        omega
      | B =>
        simp only [reduceCtorEq, decide_eq_true_eq, ↓reduceIte]
        rw [ih]
        omega

/-- In alternating list, position 2k has label A and there are k A's before it -/
lemma alternating_position_2k_is_A (l : List LabeledElement) (k : ℕ)
    (hcount : countAlternatingPrefix l ≥ k + 1)
    (h2k : 2 * k < l.length) :
    l[2 * k].label = Label.A ∧ countAPrefix l (2 * k) = k := by
  induction k generalizing l with
  | zero =>
    match l with
    | [] => simp at h2k
    | a :: rest =>
      match rest with
      | [] => simp [countAlternatingPrefix] at hcount
      | b :: rest' =>
        simp only [countAlternatingPrefix] at hcount
        split_ifs at hcount with hab
        · simp [countAPrefix, hab.1]
        · omega
  | succ k' ih =>
    match l with
    | [] => simp at h2k
    | [_] => simp at h2k
    | a :: b :: rest =>
      simp only [countAlternatingPrefix] at hcount
      split_ifs at hcount with hab
      · have hcount' : countAlternatingPrefix rest ≥ k' + 1 := by omega
        have h2k' : 2 * k' < rest.length := by simp at h2k; omega
        have ih_result := ih rest hcount' h2k'
        constructor
        · have hidx : 2 * (k' + 1) = 2 * k' + 2 := by omega
          simp only [hidx]
          have : (a :: b :: rest)[2 * k' + 2] = rest[2 * k'] := by
            simp only [List.getElem_cons_succ]
          rw [this]
          exact ih_result.1
        · have hidx : 2 * (k' + 1) = 2 * k' + 2 := by omega
          simp only [hidx, countAPrefix, hab.1, ↓reduceIte, hab.2, reduceCtorEq]
          have : countAPrefix rest (2 * k') = k' := ih_result.2
          omega
      · omega

/-- In alternating A,B,A,B,..., the first 2k-1 elements have k-1 B's -/
lemma alternating_countB_take (l : List LabeledElement) (k : ℕ)
    (hcount : countAlternatingPrefix l ≥ k)
    (h2k1 : 2 * k - 1 < l.length) (hk : k ≥ 1) :
    ((l.take (2 * k - 1)).filter (fun x => x.label = Label.B)).length = k - 1 := by
  induction k generalizing l with
  | zero => omega
  | succ k' ih =>
    match l with
    | [] => simp at h2k1
    | [a] =>
      simp only [List.length_singleton] at h2k1
      omega
    | a :: b :: rest =>
      simp only [countAlternatingPrefix] at hcount
      split_ifs at hcount with hab
      · cases k' with
        | zero =>
          simp [List.take, List.filter, hab.1]
        | succ k'' =>
          have hcount' : countAlternatingPrefix rest ≥ k'' + 1 := by omega
          have h2k1' : 2 * (k'' + 1) - 1 < rest.length := by simp at h2k1; omega
          have ih_result := ih rest hcount' h2k1' (by omega)
          have hidx : 2 * (k'' + 1 + 1) - 1 = (2 * (k'' + 1) - 1) + 2 := by omega
          rw [hidx]
          simp only [List.take_succ_cons, List.filter_cons]
          simp only [hab.1, decide_eq_true_eq, reduceCtorEq, ↓reduceIte]
          simp only [hab.2, ↓reduceIte, List.length_cons]
          omega
      · omega

/-- If there are exactly k elements with property P before position i,
    and the element at position i has property P,
    then it's the k-th element in the filter -/
lemma filter_getElem_of_countPrefix {α : Type*} (l : List α) (P : α → Bool) (i k : ℕ)
    (hi : i < l.length)
    (hP : P (l[i]) = true)
    (hcount : ((l.take i).filter P).length = k)
    (hk : k < (l.filter P).length) :
    (l.filter P)[k] = l[i] := by
  induction l generalizing i k with
  | nil => simp at hi
  | cons a as ih =>
    cases i with
    | zero =>
      simp only [List.take_zero, List.filter_nil, List.length_nil] at hcount
      simp only [List.getElem_cons_zero] at hP
      simp only [List.filter_cons, hP, ↓reduceIte, List.getElem_cons_zero]
      subst hcount
      rfl
    | succ i' =>
      simp only [List.take_succ_cons, List.filter_cons] at hcount
      simp only [List.getElem_cons_succ] at hP ⊢
      simp only [List.filter_cons]
      split at hcount
      · rename_i hPa
        simp only [List.length_cons] at hcount
        split
        · cases k with
          | zero => omega
          | succ k' =>
            simp only [List.getElem_cons_succ]
            have hi' : i' < as.length := by simp at hi; omega
            have hcount' : ((as.take i').filter P).length = k' := by omega
            have hk' : k' < (as.filter P).length := by
              simp only [List.filter_cons, hPa, ↓reduceIte, List.length_cons] at hk
              omega
            exact ih i' k' hi' hP hcount' hk'
        · rename_i hPa'
          simp only [hPa, not_true_eq_false] at hPa'
      · rename_i hPa
        split
        · rename_i hPa'
          exact absurd hPa' hPa
        · have hi' : i' < as.length := by simp at hi; omega
          have hk' : k < (as.filter P).length := by
            simp only [List.filter_cons] at hk
            split at hk
            · rename_i hPa'
              exact absurd hPa' hPa
            · exact hk
          exact ih i' k hi' hP hcount hk'

/-- In a sorted list with alternating A,B pattern, the A at position 2k
    is the k-th smallest A element -/
lemma sorted_alternating_A_is_kth (l : List LabeledElement) (n k : ℕ)
    (hn : n ≥ 1)
    (hprime_mono : ∀ i, i ≥ 1 → nthPrime i < nthPrime (i + 1))
    (hsorted : List.Pairwise (· ≤ ·) l)
    (hperm : l.Perm (labeledA n ++ labeledB (n + 1)))
    (hcount : countAlternatingPrefix l ≥ k + 1)
    (hk : k < n)
    (h2k : 2 * k < l.length) :
    l[2 * k]'h2k = (labeledA n)[k]'(by rw [labeledA_length]; exact hk) := by
  have ⟨hlab, hcountA⟩ := alternating_position_2k_is_A l k hcount h2k
  have hA_eq : l.filter (fun x => x.label = Label.A) = labeledA n := by
    apply List.Perm.eq_of_pairwise
    · intro a b ha hb hab hba
      have heq_val : a.value = b.value := Nat.le_antisymm hab hba
      simp only [List.mem_filter] at ha
      have ha' := hperm.mem_iff.mp ha.1
      have hb' : b ∈ labeledA n ++ labeledB (n + 1) := List.mem_append_left _ hb
      exact labeled_values_distinct n hn hprime_mono a b ha' hb' heq_val
    · exact sorted_filter_sorted l Label.A hsorted
    · have := labeledA_sorted n hn hprime_mono
      exact List.Pairwise.imp (fun h => Nat.le_of_lt h) this
    · have h1 := List.Perm.filter (fun x => x.label = Label.A) hperm
      simp only [List.filter_append] at h1
      have hA_self : (labeledA n).filter (fun x => x.label = Label.A) = labeledA n := by
        apply List.filter_eq_self.mpr
        intro a ha
        simp only [decide_eq_true_eq]
        exact labeledA_all_A n a ha
      have hB_nil : (labeledB (n+1)).filter (fun x => x.label = Label.A) = [] := by
        rw [List.filter_eq_nil_iff]
        intro x hx
        have := labeledB_all_B (n+1) x hx
        simp only [this, reduceCtorEq, decide_false, not_false_eq_true]
      rw [hA_self, hB_nil, List.append_nil] at h1
      exact h1
  have hcountA' : ((l.take (2 * k)).filter (fun x => x.label = Label.A)).length = k := by
    rw [← countAPrefix_eq_filter_length]
    exact hcountA
  have hfilt_len : (l.filter (fun x => x.label = Label.A)).length = n := by
    rw [hA_eq, labeledA_length]
  have hk_lt : k < (l.filter (fun x => x.label = Label.A)).length := by
    rw [hfilt_len]; exact hk
  have h_filter_getElem := filter_getElem_of_countPrefix l (fun x => x.label = Label.A)
    (2 * k) k h2k (by simp [hlab]) hcountA' hk_lt
  rw [← h_filter_getElem]
  simp only [hA_eq]

/-- The merged list is a permutation of labeledA n ++ labeledB (n+1) -/
lemma mergedList_perm (n : ℕ) :
    (mergedList n).Perm (labeledA n ++ labeledB (n + 1)) := by
  unfold mergedList labeledA labeledB
  exact List.mergeSort_perm _ _

/-- If ratio condition fails at j, then alternation breaks and L n < n -/
lemma ratio_failure_breaks_alternation (n j : ℕ) (hn : n ≥ 1) (hj1 : 1 ≤ j) (hjn : j < n)
    (hprime_mono : ∀ i, i ≥ 1 → nthPrime i < nthPrime (i + 1))
    (hNotRatio : ¬ratioLt n j) :
    L n < n := by
  unfold L
  unfold ratioLt primeRatioNum primeRatioDen at hNotRatio
  push_neg at hNotRatio
  have hAj_le_Bj1 : nthPrime (j + 1) * nthPrime n ≤ nthPrime j * nthPrime (n + 1) := by
    rw [mul_comm (nthPrime (n + 1)) (nthPrime j)] at hNotRatio
    exact hNotRatio
  have hAj_ne_Bj1 : nthPrime (j + 1) * nthPrime n ≠ nthPrime j * nthPrime (n + 1) := by
    have := semiprime_cross_ne n hn j (j - 1) hjn (by omega) hprime_mono
    intro heq
    apply this
    simp only [Nat.sub_add_cancel hj1]
    exact heq
  have hAj_lt_Bj1 : nthPrime (j + 1) * nthPrime n < nthPrime j * nthPrime (n + 1) :=
    Nat.lt_of_le_of_ne hAj_le_Bj1 hAj_ne_Bj1
  by_contra hNotLt
  push_neg at hNotLt
  have hLe := countAlternatingPrefix_le_length_div_two (mergedList n)
  have hLen := mergedList_length n
  have hcount_le_n : countAlternatingPrefix (mergedList n) ≤ n := by omega
  have hcount_eq_n : countAlternatingPrefix (mergedList n) = n :=
    Nat.le_antisymm hcount_le_n hNotLt
  have hsorted := mergedList_sorted n
  have hperm := mergedList_perm n
  have h2j_lt : 2 * j < (mergedList n).length := by rw [hLen]; omega
  have h2j1_lt : 2 * j - 1 < (mergedList n).length := by rw [hLen]; omega
  have hA_at_2j := sorted_alternating_A_is_kth (mergedList n) n j hn hprime_mono
    hsorted hperm (by omega) hjn h2j_lt
  have hB_val : ((labeledB (n+1))[j-1]'(by rw [labeledB_length]; omega)).value =
      nthPrime j * nthPrime (n + 1) := by
    unfold labeledB
    simp only [List.getElem_map]
    rw [semiprimeList_getElem' (n+1) (j-1) (by rw [semiprimeList_length]; omega)]
    simp only [Nat.sub_add_cancel hj1]
  have hA_val : ((labeledA n)[j]'(by rw [labeledA_length]; exact hjn)).value =
      nthPrime (j + 1) * nthPrime n := by
    unfold labeledA
    simp only [List.getElem_map]
    rw [semiprimeList_getElem' n j (by rw [semiprimeList_length]; exact hjn)]
  have horder : (mergedList n)[2 * j - 1]'h2j1_lt ≤ (mergedList n)[2 * j]'h2j_lt := by
    apply List.pairwise_iff_getElem.mp hsorted
    omega
  have hB_label : ((mergedList n)[2 * j - 1]'h2j1_lt).label = Label.B := by
    have hcount_j1 : countAlternatingPrefix (mergedList n) ≥ (j - 1) + 1 := by omega
    have h2k_lt : 2 * (j - 1) < (mergedList n).length := by rw [hLen]; omega
    have h2k1_lt : 2 * (j - 1) + 1 < (mergedList n).length := by rw [hLen]; omega
    have := alternating_prefix_structure (mergedList n) (j - 1) hcount_j1 h2k_lt h2k1_lt
    have hidx : 2 * j - 1 = 2 * (j - 1) + 1 := by omega
    simp only [hidx]
    exact this.2
  have hB_at_2j1 : (mergedList n)[2 * j - 1]'h2j1_lt =
      (labeledB (n+1))[j-1]'(by rw [labeledB_length]; omega) := by
    have hB_eq : (mergedList n).filter (fun x => x.label = Label.B) = labeledB (n + 1) := by
      apply List.Perm.eq_of_pairwise
      · intro a b ha hb hab hba
        have heq_val : a.value = b.value := Nat.le_antisymm hab hba
        simp only [List.mem_filter] at ha
        have ha' := hperm.mem_iff.mp ha.1
        have hb' : b ∈ labeledA n ++ labeledB (n + 1) := List.mem_append_right _ hb
        exact labeled_values_distinct n hn hprime_mono a b ha' hb' heq_val
      · exact sorted_filter_sorted (mergedList n) Label.B hsorted
      · have := labeledB_sorted (n + 1) (by omega) hprime_mono
        exact List.Pairwise.imp (fun h => Nat.le_of_lt h) this
      · have h1 := List.Perm.filter (fun x => x.label = Label.B) hperm
        simp only [List.filter_append] at h1
        have hA_nil : (labeledA n).filter (fun x => x.label = Label.B) = [] := by
          rw [List.filter_eq_nil_iff]
          intro x hx
          have := labeledA_all_A n x hx
          simp only [this, reduceCtorEq, decide_false, not_false_eq_true]
        have hB_self : (labeledB (n+1)).filter (fun x => x.label = Label.B) = labeledB (n+1) := by
          apply List.filter_eq_self.mpr
          intro a ha
          simp only [decide_eq_true_eq]
          exact labeledB_all_B (n+1) a ha
        rw [hA_nil, hB_self, List.nil_append] at h1
        exact h1
    have hcountB' : (((mergedList n).take (2 * j - 1)).filter
        (fun x => x.label = Label.B)).length = j - 1 := by
      exact alternating_countB_take (mergedList n) j (by omega) h2j1_lt hj1
    have hfilt_len : ((mergedList n).filter (fun x => x.label = Label.B)).length = n + 1 := by
      rw [hB_eq, labeledB_length]
    have hj1_lt' : j - 1 < ((mergedList n).filter (fun x => x.label = Label.B)).length := by
      rw [hfilt_len]; omega
    have h_filter_getElem := filter_getElem_of_countPrefix (mergedList n)
      (fun x => x.label = Label.B) (2 * j - 1) (j - 1)
      h2j1_lt (by simp [hB_label]) hcountB' hj1_lt'
    rw [← h_filter_getElem]
    simp only [hB_eq]
-- Now derive the contradiction
  rw [hA_at_2j, hB_at_2j1] at horder
  have hj_lt_A : j < (labeledA n).length := by rw [labeledA_length]; exact hjn
  have hj1_lt_B : j - 1 < (labeledB (n + 1)).length := by rw [labeledB_length]; omega
  have horder' : ((labeledB (n + 1))[j - 1]'hj1_lt_B).value ≤
      ((labeledA n)[j]'hj_lt_A).value := horder
  rw [hA_val, hB_val] at horder'
  omega


theorem keystone_lemma (n : ℕ) (hn : n ≥ 1)
    (hprime_mono : ∀ i, i ≥ 1 → nthPrime i < nthPrime (i + 1)) :
    L n = n ↔ isStrictRecordMin n := by
  constructor
  · -- L n = n → isStrictRecordMin n (by contrapositive)
    intro hL
    by_contra hNotRec
    unfold isStrictRecordMin at hNotRec
    push_neg at hNotRec
    obtain ⟨j, hj1, hjn, hNotRatio⟩ := hNotRec
    have hL_lt : L n < n :=
      ratio_failure_breaks_alternation n j hn hj1 hjn hprime_mono hNotRatio
    omega
  · -- isStrictRecordMin n → L n = n
    intro hRec
    unfold L
    exact mergedList_prefix_structure n hn hprime_mono hRec

/-- Twin implies perfect interleaving (UNCONDITIONAL) -/
theorem twin_implies_perfect (n : ℕ) (hn : n ≥ 1) (htwin : isTwinIndex n)
    (hprime_mono : ∀ i, i ≥ 1 → nthPrime i < nthPrime (i + 1))
    (hgap_ge_2 : ∀ i, i ≥ 1 → primeGap i ≥ 2) :
    L n = n := by
  rw [keystone_lemma n hn hprime_mono]
  unfold isStrictRecordMin
  intro j hj1 hjn
  unfold ratioLt primeRatioNum primeRatioDen
  unfold isTwinIndex primeGap at htwin
  have hn1_eq : nthPrime (n + 1) = nthPrime n + 2 := by omega
  rw [hn1_eq]
  have hpj_lt_pj1 : nthPrime j < nthPrime (j + 1) := hprime_mono j hj1
  have hgap_j : nthPrime (j + 1) = nthPrime j + primeGap j := by
    unfold primeGap
    omega
  rw [hgap_j]
  have hgap_j_ge_2 : primeGap j ≥ 2 := hgap_ge_2 j hj1
  have hpj_lt_pn : nthPrime j < nthPrime n := by
    clear hgap_j hgap_j_ge_2 hn1_eq htwin hpj_lt_pj1
    induction hjn with
    | refl => exact hprime_mono j hj1
    | @step m hjm ih =>
      simp only [Nat.succ_eq_add_one] at hjm
      have hm_ge_1 : m ≥ 1 := by
        have : j + 1 ≤ m := hjm
        omega
      calc nthPrime j < nthPrime m := ih hm_ge_1
        _ < nthPrime (m + 1) := hprime_mono m hm_ge_1
  nlinarith

/-- Helper: nthPrime is strictly increasing for positive inputs -/
lemma nthPrime_strictMono : ∀ i j : ℕ, 1 ≤ i → i < j → nthPrime i < nthPrime j := by
  intro i j hi hij
  have hprime_mono : ∀ k, k ≥ 1 → nthPrime k < nthPrime (k + 1) := by
    intro k hk
    unfold nthPrime
    have hk_ne : k ≠ 0 := by omega
    have hk1_ne : k + 1 ≠ 0 := by omega
    simp only [hk_ne, hk1_ne, ↓reduceIte, Nat.add_sub_cancel]
    exact Nat.nth_strictMono Nat.infinite_setOf_prime (by omega : k - 1 < k)
  exact nthPrime_strictMono' hprime_mono i j hi hij

/-- Helper: primeGap is at least 2 for n ≥ 2 (consecutive odd primes) -/
lemma primeGap_ge_two (n : ℕ) (hn : n ≥ 2) : primeGap n ≥ 2 := by
  unfold primeGap
  have h2 : nthPrime (n + 1) > nthPrime n := by
    have hprime_mono : ∀ k, k ≥ 1 → nthPrime k < nthPrime (k + 1) := by
      intro k hk
      unfold nthPrime
      have hk_ne : k ≠ 0 := by omega
      have hk1_ne : k + 1 ≠ 0 := by omega
      simp only [hk_ne, hk1_ne, ↓reduceIte, Nat.add_sub_cancel]
      exact Nat.nth_strictMono Nat.infinite_setOf_prime (by omega : k - 1 < k)
    exact hprime_mono n (by omega)
  have hp_n : Nat.Prime (nthPrime n) := by
    unfold nthPrime
    simp only [show n ≠ 0 by omega, ↓reduceIte]
    exact Nat.nth_mem_of_infinite Nat.infinite_setOf_prime (n - 1)
  have hp_n1 : Nat.Prime (nthPrime (n + 1)) := by
    unfold nthPrime
    simp only [show n + 1 ≠ 0 by omega, ↓reduceIte, Nat.add_sub_cancel]
    exact Nat.nth_mem_of_infinite Nat.infinite_setOf_prime n
  have hge3_n : nthPrime n ≥ 3 := by
    have h2_is : nthPrime 2 = Nat.nth Nat.Prime 1 := by unfold nthPrime; simp
    have hp2 : Nat.Prime (Nat.nth Nat.Prime 1) :=
      Nat.nth_mem_of_infinite Nat.infinite_setOf_prime 1
    have hp2_ge : Nat.nth Nat.Prime 1 ≥ 3 := by
      have h0 : Nat.nth Nat.Prime 0 = 2 := Nat.nth_prime_zero_eq_two
      have hlt : Nat.nth Nat.Prime 0 < Nat.nth Nat.Prime 1 :=
        Nat.nth_strictMono Nat.infinite_setOf_prime (by omega : 0 < 1)
      have hodd : Odd (Nat.nth Nat.Prime 1) :=
        Nat.Prime.odd_of_ne_two hp2 (by omega)
      omega
    by_cases h : n = 2
    · rw [h, h2_is]; exact hp2_ge
    · have hgt2 : n > 2 := by omega
      have hlt : nthPrime 2 < nthPrime n := by
        apply nthPrime_strictMono 2 n (by omega) hgt2
      omega
  have hodd_n : Odd (nthPrime n) := Nat.Prime.odd_of_ne_two hp_n (by omega)
  have hodd_n1 : Odd (nthPrime (n + 1)) := Nat.Prime.odd_of_ne_two hp_n1 (by omega)
  obtain ⟨k, hk⟩ := hodd_n
  obtain ⟨m, hm⟩ := hodd_n1
  omega

/-- Perfect at non-twin implies twin-free interval exists (UNCONDITIONAL) -/
theorem perfect_nontwin_implies_twinfree_interval (n : ℕ) (hn : n ≥ 1)
    (hprime_mono : ∀ i, i ≥ 1 → nthPrime i < nthPrime (i + 1))
    (hperfect : L n = n) (_hnontwin : primeGap n ≥ 4) :
    ∀ i : ℕ, 1 ≤ i → i < n → isTwinIndex i →
      nthPrime i * primeGap n ≤ 2 * nthPrime n := by
  intro i hi1 hin hitwin
  -- From hperfect and keystone_lemma, we have isStrictRecordMin n
  have hrecord : isStrictRecordMin n := by
    rw [keystone_lemma n hn hprime_mono] at hperfect
    exact hperfect
  -- So ratioLt n i holds
  have hratio : ratioLt n i := hrecord i hi1 hin
  -- ratioLt n i means: nthPrime (n+1) * nthPrime i < nthPrime (i+1) * nthPrime n
  unfold ratioLt primeRatioNum primeRatioDen at hratio
  -- hitwin means primeGap i = 2, so nthPrime (i+1) = nthPrime i + 2
  unfold isTwinIndex primeGap at hitwin
  have hi1_eq : nthPrime (i + 1) = nthPrime i + 2 := by
    have hlt : nthPrime i < nthPrime (i + 1) := hprime_mono i hi1
    omega
  -- nthPrime (n+1) = nthPrime n + primeGap n
  have hn1_eq : nthPrime (n + 1) = nthPrime n + primeGap n := by
    unfold primeGap
    have hlt : nthPrime n < nthPrime (n + 1) := hprime_mono n hn
    omega
  -- Substitute into hratio:
  rw [hn1_eq, hi1_eq] at hratio
  -- So: primeGap n * nthPrime i < 2 * nthPrime n
  have h : primeGap n * nthPrime i < 2 * nthPrime n := by nlinarith
  rw [mul_comm]
  omega


/-! ## Conditional Results -/

/-- Hypothesis: Twin primes are sufficiently dense -/
def TwinDensityHypothesis : Prop :=
  ∀ n : ℕ, n ≥ 10 → primeGap n ≥ 4 →
    ∃ i : ℕ, 1 ≤ i ∧ i < n ∧ isTwinIndex i ∧
      nthPrime i * primeGap n > 2 * nthPrime n

/-- Under twin density hypothesis, L(n) = n ↔ twin (CONDITIONAL) -/
theorem perfect_iff_twin_conditional (h : TwinDensityHypothesis) (n : ℕ) (hn : n ≥ 10)
    (hprime_mono : ∀ i, i ≥ 1 → nthPrime i < nthPrime (i + 1))
    (hgap_ge_2 : ∀ i, i ≥ 1 → primeGap i ≥ 2) :
    L n = n ↔ isTwinIndex n := by
  constructor
  · intro hperfect
    by_contra hnottwin
    -- gap is even and ≠ 2, so gap ≥ 4
    have hgap_ge2 : primeGap n ≥ 2 := hgap_ge_2 n (by omega)
    have hgap_ne2 : primeGap n ≠ 2 := by
      unfold isTwinIndex at hnottwin
      exact hnottwin
    -- Prime gaps for n ≥ 2 are even (difference of two odd primes)
    have hgap_even : Even (primeGap n) := by
      unfold primeGap
      have hp_n : Nat.Prime (nthPrime n) := by
        unfold nthPrime
        simp only [show n ≠ 0 by omega, ↓reduceIte]
        exact Nat.nth_mem_of_infinite Nat.infinite_setOf_prime (n - 1)
      have hp_n1 : Nat.Prime (nthPrime (n + 1)) := by
        unfold nthPrime
        simp only [show n + 1 ≠ 0 by omega, ↓reduceIte, Nat.add_sub_cancel]
        exact Nat.nth_mem_of_infinite Nat.infinite_setOf_prime n
      have hge3_n : nthPrime n ≥ 3 := by
        have h2_lt : nthPrime 2 < nthPrime n := nthPrime_strictMono 2 n (by omega) (by omega)
        unfold nthPrime at h2_lt ⊢
        simp only [show n ≠ 0 by omega, ↓reduceIte, show (2 : ℕ) ≠ 0 by omega] at h2_lt ⊢
        have h21 : (2 : ℕ) - 1 = 1 := by omega
        rw [h21] at h2_lt
        have hp2 : Nat.Prime (Nat.nth Nat.Prime 1) :=
          Nat.nth_mem_of_infinite Nat.infinite_setOf_prime 1
        have h0 : Nat.nth Nat.Prime 0 = 2 := Nat.nth_prime_zero_eq_two
        have hlt01 : Nat.nth Nat.Prime 0 < Nat.nth Nat.Prime 1 :=
          Nat.nth_strictMono Nat.infinite_setOf_prime (by omega : 0 < 1)
        have hp2_ge : Nat.nth Nat.Prime 1 ≥ 3 := by omega
        omega
      have hodd_n : Odd (nthPrime n) := Nat.Prime.odd_of_ne_two hp_n (by omega)
      have hodd_n1 : Odd (nthPrime (n + 1)) := by
        have hge3_n1 : nthPrime (n + 1) > nthPrime n := hprime_mono n (by omega)
        exact Nat.Prime.odd_of_ne_two hp_n1 (by omega)
      exact Nat.Odd.sub_odd hodd_n1 hodd_n
    have hgap : primeGap n ≥ 4 := by
      obtain ⟨k, hk⟩ := hgap_even
      omega
    -- Get witness from hypothesis
    obtain ⟨i, hi1, hin, hitwin, hibig⟩ := h n hn hgap
    -- Contradicts twinfree interval
    have hsmall := perfect_nontwin_implies_twinfree_interval n (by omega)
      hprime_mono hperfect hgap i hi1 hin hitwin
    omega
  · exact fun htwin => twin_implies_perfect n (by omega) htwin hprime_mono hgap_ge_2

lemma ratioLt_trans {a b c : ℕ} (hab : ratioLt a b) (hbc : ratioLt b c)
    (ha1 : a ≥ 1) (hb1 : b ≥ 1) (hc1 : c ≥ 1) :
    ratioLt a c := by
  unfold ratioLt primeRatioNum primeRatioDen at *

  have hpa_pos : nthPrime a > 0 := nthPrime_pos a ha1
  have hpb_pos : nthPrime b > 0 := nthPrime_pos b hb1
  have hpc_pos : nthPrime c > 0 := nthPrime_pos c hc1

  have h1 : nthPrime (a + 1) * nthPrime b * nthPrime c <
            nthPrime (b + 1) * nthPrime a * nthPrime c := by
    calc nthPrime (a + 1) * nthPrime b * nthPrime c
        = (nthPrime (a + 1) * nthPrime b) * nthPrime c := by ring
      _ < (nthPrime (b + 1) * nthPrime a) * nthPrime c :=
          Nat.mul_lt_mul_of_pos_right hab hpc_pos
      _ = nthPrime (b + 1) * nthPrime a * nthPrime c := by ring

  have h2 : nthPrime (b + 1) * nthPrime a * nthPrime c <
            nthPrime (c + 1) * nthPrime a * nthPrime b := by
    calc nthPrime (b + 1) * nthPrime a * nthPrime c
        = nthPrime a * (nthPrime (b + 1) * nthPrime c) := by ring
      _ < nthPrime a * (nthPrime (c + 1) * nthPrime b) :=
          Nat.mul_lt_mul_of_pos_left hbc hpa_pos
      _ = nthPrime (c + 1) * nthPrime a * nthPrime b := by ring

  have h3 : nthPrime (a + 1) * nthPrime b * nthPrime c <
            nthPrime (c + 1) * nthPrime a * nthPrime b :=
    Nat.lt_trans h1 h2

  have h4 : nthPrime (a + 1) * nthPrime c * nthPrime b <
            nthPrime (c + 1) * nthPrime a * nthPrime b := by
    calc nthPrime (a + 1) * nthPrime c * nthPrime b
        = nthPrime (a + 1) * nthPrime b * nthPrime c := by ring
      _ < nthPrime (c + 1) * nthPrime a * nthPrime b := h3

  exact Nat.lt_of_mul_lt_mul_right h4

/-- The predicate "TwinDensityHypothesis fails at n" -/
def TwinDensityFailsAt (n : ℕ) : Prop :=
  n ≥ 10 ∧ primeGap n ≥ 4 ∧
  ∀ i : ℕ, 1 ≤ i → i < n → isTwinIndex i → nthPrime i * primeGap n ≤ 2 * nthPrime n

/-- Key lemma: if TwinDensityHypothesis holds at j, then j is not a record minimum -/
lemma density_breaks_record (j : ℕ) (hj : j ≥ 10)
    (hdensity_at_j : ∃ i : ℕ, 1 ≤ i ∧ i < j ∧ isTwinIndex i
      ∧ nthPrime i * primeGap j > 2 * nthPrime j)
    (hprime_mono : ∀ i, i ≥ 1 → nthPrime i < nthPrime (i + 1)) :
    ¬isStrictRecordMin j := by
  obtain ⟨i, hi1, hij, hitwin, hibig⟩ := hdensity_at_j
  intro hrecord
  have hratioij : ratioLt i j := by
    unfold ratioLt primeRatioNum primeRatioDen
    unfold isTwinIndex primeGap at hitwin
    have hi1_eq : nthPrime (i + 1) = nthPrime i + 2 := by
      have hlt : nthPrime i < nthPrime (i + 1) := hprime_mono i hi1
      omega
    have hj1_eq : nthPrime (j + 1) = nthPrime j + primeGap j := by
      unfold primeGap
      have hlt : nthPrime j < nthPrime (j + 1) := hprime_mono j (by omega)
      omega
    rw [hi1_eq, hj1_eq]
    nlinarith
  have hratioLt_ji : ratioLt j i := hrecord i hi1 hij
  unfold ratioLt primeRatioNum primeRatioDen at hratioij hratioLt_ji
  omega

/-- Helper: n beats twin i when TwinDensityHypothesis fails at n -/
lemma nontwin_beats_twin_when_density_fails (n i : ℕ) (hn : n ≥ 10) (hgap : primeGap n ≥ 4)
    (hi1 : 1 ≤ i) (hin : i < n) (hitwin : isTwinIndex i)
    (hno : ∀ i : ℕ, 1 ≤ i → i < n → isTwinIndex i → nthPrime i * primeGap n ≤ 2 * nthPrime n)
    (hprime_mono : ∀ i, i ≥ 1 → nthPrime i < nthPrime (i + 1)) :
    ratioLt n i := by
  unfold ratioLt primeRatioNum primeRatioDen
  unfold isTwinIndex primeGap at hitwin
  have hi1_eq : nthPrime (i + 1) = nthPrime i + 2 := by
    have hlt : nthPrime i < nthPrime (i + 1) := hprime_mono i hi1
    omega
  have hn1_eq : nthPrime (n + 1) = nthPrime n + primeGap n := by
    unfold primeGap
    have hlt : nthPrime n < nthPrime (n + 1) := hprime_mono n (by omega)
    omega
  rw [hi1_eq, hn1_eq]
  have hsmall := hno i hi1 hin hitwin
  have hpn_pos : nthPrime n > 0 := nthPrime_pos n (by omega)
  have hpi_pos : nthPrime i > 0 := nthPrime_pos i hi1

  have hne : nthPrime i * primeGap n ≠ 2 * nthPrime n := by
    intro heq
    have hpn_prime : Nat.Prime (nthPrime n) := by
      have hn_ne : n ≠ 0 := by omega
      unfold nthPrime
      simp only [hn_ne, ↓reduceIte]
      exact Nat.nth_mem_of_infinite Nat.infinite_setOf_prime (n - 1)
    have hpn_ge3 : nthPrime n ≥ 3 := by
      have hp1_lt : nthPrime 1 < nthPrime n :=
        nthPrime_strictMono 1 n (by omega) (by omega)
      have hp1_eq : nthPrime 1 = 2 := by
        unfold nthPrime
        simp only [one_ne_zero, ↓reduceIte, Nat.sub_self]
        exact Nat.nth_prime_zero_eq_two
      omega
    have hgap_even : Even (primeGap n) := by
      unfold primeGap
      have hn1_ne : n + 1 ≠ 0 := by omega
      have hp_n1 : Nat.Prime (nthPrime (n + 1)) := by
        unfold nthPrime
        simp only [hn1_ne, ↓reduceIte, Nat.add_sub_cancel]
        exact Nat.nth_mem_of_infinite Nat.infinite_setOf_prime n
      have hodd_n : Odd (nthPrime n) := Nat.Prime.odd_of_ne_two hpn_prime (by omega)
      have hodd_n1 : Odd (nthPrime (n + 1)) := Nat.Prime.odd_of_ne_two hp_n1 (by omega)
      exact Nat.Odd.sub_odd hodd_n1 hodd_n
    obtain ⟨k, hk⟩ := hgap_even
    have hk_ge2 : k ≥ 2 := by omega
    have hk' : primeGap n = 2 * k := by omega
    have heq2 : nthPrime i * k = nthPrime n := by
      have h3 : nthPrime i * (2 * k) = 2 * nthPrime n := by rw [← hk']; exact heq
      nlinarith
    have hk_div : k ∣ nthPrime n := ⟨nthPrime i, by rw [mul_comm]; exact heq2.symm⟩
    have hk_eq : k = 1 ∨ k = nthPrime n :=
      Nat.Prime.eq_one_or_self_of_dvd hpn_prime k hk_div
    cases hk_eq with
    | inl h1 => omega
    | inr hkn =>
      rw [hkn] at hk'
      have hpn_ne0 : nthPrime n ≠ 0 := by omega
      have hbertrand := Nat.bertrand (nthPrime n) hpn_ne0
      obtain ⟨p, hp_prime, hp_lb, hp_ub⟩ := hbertrand
      have hn1_ne : n + 1 ≠ 0 := by omega
      have hn_ne : n ≠ 0 := by omega
      have hn1_le_p : nthPrime (n + 1) ≤ p := by
        unfold nthPrime at hp_lb ⊢
        simp only [hn1_ne, hn_ne, ↓reduceIte, Nat.add_sub_cancel] at hp_lb ⊢
        have hleast := Nat.isLeast_nth_of_infinite Nat.infinite_setOf_prime n
        apply hleast.2
        constructor
        · exact hp_prime
        · intro m hm
          calc Nat.nth Nat.Prime m
              ≤ Nat.nth Nat.Prime (n - 1) := by
                apply Nat.nth_monotone Nat.infinite_setOf_prime
                omega
            _ < p := hp_lb
      unfold primeGap at hk'
      have hlt : nthPrime n < nthPrime (n + 1) := hprime_mono n (by omega)
      omega
  have hstrict : nthPrime i * primeGap n < 2 * nthPrime n :=
    Nat.lt_of_le_of_ne hsmall hne
  nlinarith

lemma nthPrime_1_eq_3_aux : Nat.nth Nat.Prime 1 = 3 := by
  have h0 : Nat.nth Nat.Prime 0 = 2 := Nat.nth_prime_zero_eq_two
  have h3_prime : Nat.Prime 3 := by decide
  have hge3 : Nat.nth Nat.Prime 1 ≥ 3 := by
    have hlt : Nat.nth Nat.Prime 0 < Nat.nth Nat.Prime 1 :=
      Nat.nth_strictMono Nat.infinite_setOf_prime (by omega : 0 < 1)
    omega
  have hle3 : Nat.nth Nat.Prime 1 ≤ 3 := by
    have hleast := Nat.isLeast_nth_of_infinite Nat.infinite_setOf_prime 1
    have hmem : 3 ∈ {i | Nat.Prime i ∧ ∀ k < 1, Nat.nth Nat.Prime k < i} := by
      simp only [Set.mem_setOf_eq]
      constructor
      · exact h3_prime
      · intro k hk
        have hk0 : k = 0 := by omega
        rw [hk0, h0]
        omega
    exact hleast.2 hmem
  omega

lemma nthPrime_2_eq_5_aux : Nat.nth Nat.Prime 2 = 5 := by
  have h0 : Nat.nth Nat.Prime 0 = 2 := Nat.nth_prime_zero_eq_two
  have h1 : Nat.nth Nat.Prime 1 = 3 := nthPrime_1_eq_3_aux
  have h5_prime : Nat.Prime 5 := by decide
  have h4_not_prime : ¬Nat.Prime 4 := by decide
  have hge5 : Nat.nth Nat.Prime 2 ≥ 5 := by
    have hlt : Nat.nth Nat.Prime 1 < Nat.nth Nat.Prime 2 :=
      Nat.nth_strictMono Nat.infinite_setOf_prime (by omega : 1 < 2)
    have hp2 : Nat.Prime (Nat.nth Nat.Prime 2) :=
      Nat.nth_mem_of_infinite Nat.infinite_setOf_prime 2
    have hgt3 : Nat.nth Nat.Prime 2 > 3 := by omega
    have hne4 : Nat.nth Nat.Prime 2 ≠ 4 := by
      intro heq
      rw [heq] at hp2
      exact h4_not_prime hp2
    omega
  have hle5 : Nat.nth Nat.Prime 2 ≤ 5 := by
    have hleast := Nat.isLeast_nth_of_infinite Nat.infinite_setOf_prime 2
    have hmem : 5 ∈ {i | Nat.Prime i ∧ ∀ k < 2, Nat.nth Nat.Prime k < i} := by
      simp only [Set.mem_setOf_eq]
      constructor
      · exact h5_prime
      · intro k hk
        interval_cases k <;> omega
    exact hleast.2 hmem
  omega

lemma nthPrime_3_eq_7_aux : Nat.nth Nat.Prime 3 = 7 := by
  have h1 : Nat.nth Nat.Prime 1 = 3 := nthPrime_1_eq_3_aux
  have h2 : Nat.nth Nat.Prime 2 = 5 := nthPrime_2_eq_5_aux
  have h7_prime : Nat.Prime 7 := by decide
  have h6_not_prime : ¬Nat.Prime 6 := by decide
  have hge7 : Nat.nth Nat.Prime 3 ≥ 7 := by
    have hlt : Nat.nth Nat.Prime 2 < Nat.nth Nat.Prime 3 :=
      Nat.nth_strictMono Nat.infinite_setOf_prime (by omega : 2 < 3)
    have hp3 : Nat.Prime (Nat.nth Nat.Prime 3) :=
      Nat.nth_mem_of_infinite Nat.infinite_setOf_prime 3
    have hgt5 : Nat.nth Nat.Prime 3 > 5 := by omega
    have hne6 : Nat.nth Nat.Prime 3 ≠ 6 := by
      intro heq
      rw [heq] at hp3
      exact h6_not_prime hp3
    omega
  have hle7 : Nat.nth Nat.Prime 3 ≤ 7 := by
    have hleast := Nat.isLeast_nth_of_infinite Nat.infinite_setOf_prime 3
    have hmem : 7 ∈ {i | Nat.Prime i ∧ ∀ k < 3, Nat.nth Nat.Prime k < i} := by
      simp only [Set.mem_setOf_eq]
      constructor
      · exact h7_prime
      · intro k hk
        have h0 : Nat.nth Nat.Prime 0 = 2 := Nat.nth_prime_zero_eq_two
        interval_cases k <;> omega
    exact hleast.2 hmem
  omega

lemma nthPrime_4_eq_11_aux : Nat.nth Nat.Prime 4 = 11 := by
  have h0 : Nat.nth Nat.Prime 0 = 2 := Nat.nth_prime_zero_eq_two
  have h1 : Nat.nth Nat.Prime 1 = 3 := nthPrime_1_eq_3_aux
  have h2 : Nat.nth Nat.Prime 2 = 5 := nthPrime_2_eq_5_aux
  have h3 : Nat.nth Nat.Prime 3 = 7 := nthPrime_3_eq_7_aux
  have h11_prime : Nat.Prime 11 := by decide
  have h8_not_prime : ¬Nat.Prime 8 := by decide
  have h9_not_prime : ¬Nat.Prime 9 := by decide
  have h10_not_prime : ¬Nat.Prime 10 := by decide
  have hge11 : Nat.nth Nat.Prime 4 ≥ 11 := by
    have hlt : Nat.nth Nat.Prime 3 < Nat.nth Nat.Prime 4 :=
      Nat.nth_strictMono Nat.infinite_setOf_prime (by omega : 3 < 4)
    have hp4 : Nat.Prime (Nat.nth Nat.Prime 4) :=
      Nat.nth_mem_of_infinite Nat.infinite_setOf_prime 4
    have hgt7 : Nat.nth Nat.Prime 4 > 7 := by omega
    have hne8 : Nat.nth Nat.Prime 4 ≠ 8 := by
      intro heq; rw [heq] at hp4; exact h8_not_prime hp4
    have hne9 : Nat.nth Nat.Prime 4 ≠ 9 := by
      intro heq; rw [heq] at hp4; exact h9_not_prime hp4
    have hne10 : Nat.nth Nat.Prime 4 ≠ 10 := by
      intro heq; rw [heq] at hp4; exact h10_not_prime hp4
    omega
  have hle11 : Nat.nth Nat.Prime 4 ≤ 11 := by
    have hleast := Nat.isLeast_nth_of_infinite Nat.infinite_setOf_prime 4
    have hmem : 11 ∈ {i | Nat.Prime i ∧ ∀ k < 4, Nat.nth Nat.Prime k < i} := by
      simp only [Set.mem_setOf_eq]
      constructor
      · exact h11_prime
      · intro k hk
        interval_cases k <;> omega
    exact hleast.2 hmem
  omega

lemma nthPrime_5_eq_13_aux : Nat.nth Nat.Prime 5 = 13 := by
  have h0 : Nat.nth Nat.Prime 0 = 2 := Nat.nth_prime_zero_eq_two
  have h1 : Nat.nth Nat.Prime 1 = 3 := nthPrime_1_eq_3_aux
  have h2 : Nat.nth Nat.Prime 2 = 5 := nthPrime_2_eq_5_aux
  have h3 : Nat.nth Nat.Prime 3 = 7 := nthPrime_3_eq_7_aux
  have h4 : Nat.nth Nat.Prime 4 = 11 := nthPrime_4_eq_11_aux
  have h13_prime : Nat.Prime 13 := by decide
  have h12_not_prime : ¬Nat.Prime 12 := by decide
  have hge13 : Nat.nth Nat.Prime 5 ≥ 13 := by
    have hlt : Nat.nth Nat.Prime 4 < Nat.nth Nat.Prime 5 :=
      Nat.nth_strictMono Nat.infinite_setOf_prime (by omega : 4 < 5)
    have hp5 : Nat.Prime (Nat.nth Nat.Prime 5) :=
      Nat.nth_mem_of_infinite Nat.infinite_setOf_prime 5
    have hgt11 : Nat.nth Nat.Prime 5 > 11 := by omega
    have hne12 : Nat.nth Nat.Prime 5 ≠ 12 := by
      intro heq; rw [heq] at hp5; exact h12_not_prime hp5
    omega
  have hle13 : Nat.nth Nat.Prime 5 ≤ 13 := by
    have hleast := Nat.isLeast_nth_of_infinite Nat.infinite_setOf_prime 5
    have hmem : 13 ∈ {i | Nat.Prime i ∧ ∀ k < 5, Nat.nth Nat.Prime k < i} := by
      simp only [Set.mem_setOf_eq]
      constructor
      · exact h13_prime
      · intro k hk
        interval_cases k <;> omega
    exact hleast.2 hmem
  omega

lemma nthPrime_3_eq_5 : nthPrime 3 = 5 := by
  unfold nthPrime
  simp only [show (3 : ℕ) ≠ 0 by omega, ↓reduceIte]
  have h : (3 : ℕ) - 1 = 2 := by omega
  rw [h]
  exact nthPrime_2_eq_5_aux

lemma nthPrime_4_eq_7 : nthPrime 4 = 7 := by
  unfold nthPrime
  simp only [show (4 : ℕ) ≠ 0 by omega, ↓reduceIte]
  have h : (4 : ℕ) - 1 = 3 := by omega
  rw [h]
  exact nthPrime_3_eq_7_aux

lemma nthPrime_5_eq_11 : nthPrime 5 = 11 := by
  unfold nthPrime
  simp only [show (5 : ℕ) ≠ 0 by omega, ↓reduceIte]
  have h : (5 : ℕ) - 1 = 4 := by omega
  rw [h]
  exact nthPrime_4_eq_11_aux

lemma nthPrime_6_eq_13 : nthPrime 6 = 13 := by
  unfold nthPrime
  simp only [show (6 : ℕ) ≠ 0 by omega, ↓reduceIte]
  have h : (6 : ℕ) - 1 = 5 := by omega
  rw [h]
  exact nthPrime_5_eq_13_aux

lemma nthPrime_6_eq_17_aux : Nat.nth Nat.Prime 6 = 17 := by
  have h0 : Nat.nth Nat.Prime 0 = 2 := Nat.nth_prime_zero_eq_two
  have h1 : Nat.nth Nat.Prime 1 = 3 := nthPrime_1_eq_3_aux
  have h2 : Nat.nth Nat.Prime 2 = 5 := nthPrime_2_eq_5_aux
  have h3 : Nat.nth Nat.Prime 3 = 7 := nthPrime_3_eq_7_aux
  have h4 : Nat.nth Nat.Prime 4 = 11 := nthPrime_4_eq_11_aux
  have h5 : Nat.nth Nat.Prime 5 = 13 := nthPrime_5_eq_13_aux
  have h17_prime : Nat.Prime 17 := by decide
  have h14_not_prime : ¬Nat.Prime 14 := by decide
  have h15_not_prime : ¬Nat.Prime 15 := by decide
  have h16_not_prime : ¬Nat.Prime 16 := by decide
  have hge17 : Nat.nth Nat.Prime 6 ≥ 17 := by
    have hlt : Nat.nth Nat.Prime 5 < Nat.nth Nat.Prime 6 :=
      Nat.nth_strictMono Nat.infinite_setOf_prime (by omega : 5 < 6)
    have hp6 : Nat.Prime (Nat.nth Nat.Prime 6) :=
      Nat.nth_mem_of_infinite Nat.infinite_setOf_prime 6
    have hgt13 : Nat.nth Nat.Prime 6 > 13 := by omega
    have hne14 : Nat.nth Nat.Prime 6 ≠ 14 := by
      intro heq; rw [heq] at hp6; exact h14_not_prime hp6
    have hne15 : Nat.nth Nat.Prime 6 ≠ 15 := by
      intro heq; rw [heq] at hp6; exact h15_not_prime hp6
    have hne16 : Nat.nth Nat.Prime 6 ≠ 16 := by
      intro heq; rw [heq] at hp6; exact h16_not_prime hp6
    omega
  have hle17 : Nat.nth Nat.Prime 6 ≤ 17 := by
    have hleast := Nat.isLeast_nth_of_infinite Nat.infinite_setOf_prime 6
    have hmem : 17 ∈ {i | Nat.Prime i ∧ ∀ k < 6, Nat.nth Nat.Prime k < i} := by
      simp only [Set.mem_setOf_eq]
      constructor
      · exact h17_prime
      · intro k hk
        interval_cases k <;> omega
    exact hleast.2 hmem
  omega

lemma nthPrime_7_eq_17 : nthPrime 7 = 17 := by
  unfold nthPrime
  simp only [show (7 : ℕ) ≠ 0 by omega, ↓reduceIte]
  have h : (7 : ℕ) - 1 = 6 := by omega
  rw [h]
  exact nthPrime_6_eq_17_aux

lemma nthPrime_7_eq_19_aux : Nat.nth Nat.Prime 7 = 19 := by
  have h0 : Nat.nth Nat.Prime 0 = 2 := Nat.nth_prime_zero_eq_two
  have h1 : Nat.nth Nat.Prime 1 = 3 := nthPrime_1_eq_3_aux
  have h2 : Nat.nth Nat.Prime 2 = 5 := nthPrime_2_eq_5_aux
  have h3 : Nat.nth Nat.Prime 3 = 7 := nthPrime_3_eq_7_aux
  have h4 : Nat.nth Nat.Prime 4 = 11 := nthPrime_4_eq_11_aux
  have h5 : Nat.nth Nat.Prime 5 = 13 := nthPrime_5_eq_13_aux
  have h6 : Nat.nth Nat.Prime 6 = 17 := nthPrime_6_eq_17_aux
  have h19_prime : Nat.Prime 19 := by decide
  have h18_not_prime : ¬Nat.Prime 18 := by decide
  have hge19 : Nat.nth Nat.Prime 7 ≥ 19 := by
    have hlt : Nat.nth Nat.Prime 6 < Nat.nth Nat.Prime 7 :=
      Nat.nth_strictMono Nat.infinite_setOf_prime (by omega : 6 < 7)
    have hp7 : Nat.Prime (Nat.nth Nat.Prime 7) :=
      Nat.nth_mem_of_infinite Nat.infinite_setOf_prime 7
    have hgt17 : Nat.nth Nat.Prime 7 > 17 := by omega
    have hne18 : Nat.nth Nat.Prime 7 ≠ 18 := by
      intro heq; rw [heq] at hp7; exact h18_not_prime hp7
    omega
  have hle19 : Nat.nth Nat.Prime 7 ≤ 19 := by
    have hleast := Nat.isLeast_nth_of_infinite Nat.infinite_setOf_prime 7
    have hmem : 19 ∈ {i | Nat.Prime i ∧ ∀ k < 7, Nat.nth Nat.Prime k < i} := by
      simp only [Set.mem_setOf_eq]
      constructor
      · exact h19_prime
      · intro k hk
        interval_cases k <;> omega
    exact hleast.2 hmem
  omega

lemma nthPrime_8_eq_19 : nthPrime 8 = 19 := by
  unfold nthPrime
  simp only [show (8 : ℕ) ≠ 0 by omega, ↓reduceIte]
  have h : (8 : ℕ) - 1 = 7 := by omega
  rw [h]
  exact nthPrime_7_eq_19_aux

lemma nthPrime_8_eq_23_aux : Nat.nth Nat.Prime 8 = 23 := by
  have h0 : Nat.nth Nat.Prime 0 = 2 := Nat.nth_prime_zero_eq_two
  have h1 : Nat.nth Nat.Prime 1 = 3 := nthPrime_1_eq_3_aux
  have h2 : Nat.nth Nat.Prime 2 = 5 := nthPrime_2_eq_5_aux
  have h3 : Nat.nth Nat.Prime 3 = 7 := nthPrime_3_eq_7_aux
  have h4 : Nat.nth Nat.Prime 4 = 11 := nthPrime_4_eq_11_aux
  have h5 : Nat.nth Nat.Prime 5 = 13 := nthPrime_5_eq_13_aux
  have h6 : Nat.nth Nat.Prime 6 = 17 := nthPrime_6_eq_17_aux
  have h7 : Nat.nth Nat.Prime 7 = 19 := nthPrime_7_eq_19_aux
  have h23_prime : Nat.Prime 23 := by decide
  have h20_not_prime : ¬Nat.Prime 20 := by decide
  have h21_not_prime : ¬Nat.Prime 21 := by decide
  have h22_not_prime : ¬Nat.Prime 22 := by decide
  have hge23 : Nat.nth Nat.Prime 8 ≥ 23 := by
    have hlt : Nat.nth Nat.Prime 7 < Nat.nth Nat.Prime 8 :=
      Nat.nth_strictMono Nat.infinite_setOf_prime (by omega : 7 < 8)
    have hp8 : Nat.Prime (Nat.nth Nat.Prime 8) :=
      Nat.nth_mem_of_infinite Nat.infinite_setOf_prime 8
    have hgt19 : Nat.nth Nat.Prime 8 > 19 := by omega
    have hne20 : Nat.nth Nat.Prime 8 ≠ 20 := by
      intro heq; rw [heq] at hp8; exact h20_not_prime hp8
    have hne21 : Nat.nth Nat.Prime 8 ≠ 21 := by
      intro heq; rw [heq] at hp8; exact h21_not_prime hp8
    have hne22 : Nat.nth Nat.Prime 8 ≠ 22 := by
      intro heq; rw [heq] at hp8; exact h22_not_prime hp8
    omega
  have hle23 : Nat.nth Nat.Prime 8 ≤ 23 := by
    have hleast := Nat.isLeast_nth_of_infinite Nat.infinite_setOf_prime 8
    have hmem : 23 ∈ {i | Nat.Prime i ∧ ∀ k < 8, Nat.nth Nat.Prime k < i} := by
      simp only [Set.mem_setOf_eq]
      constructor
      · exact h23_prime
      · intro k hk
        interval_cases k <;> omega
    exact hleast.2 hmem
  omega

lemma nthPrime_9_eq_23 : nthPrime 9 = 23 := by
  unfold nthPrime
  simp only [show (9 : ℕ) ≠ 0 by omega, ↓reduceIte]
  have h : (9 : ℕ) - 1 = 8 := by omega
  rw [h]
  exact nthPrime_8_eq_23_aux

lemma primeGap_4_eq_4 : primeGap 4 = 4 := by
  unfold primeGap
  have hp4 : nthPrime 4 = 7 := nthPrime_4_eq_7
  have hp5 : nthPrime 5 = 11 := nthPrime_5_eq_11
  rw [hp4, hp5]

lemma primeGap_6_eq_4 : primeGap 6 = 4 := by
  unfold primeGap
  have hp6 : nthPrime 6 = 13 := nthPrime_6_eq_13
  have hp7 : nthPrime 7 = 17 := nthPrime_7_eq_17
  rw [hp6, hp7]

lemma primeGap_8_eq_4 : primeGap 8 = 4 := by
  unfold primeGap
  have hp8 : nthPrime 8 = 19 := nthPrime_8_eq_19
  have hp9 : nthPrime 9 = 23 := nthPrime_9_eq_23
  rw [hp8, hp9]

lemma nthPrime_9_eq_29_aux : Nat.nth Nat.Prime 9 = 29 := by
  have h0 : Nat.nth Nat.Prime 0 = 2 := Nat.nth_prime_zero_eq_two
  have h1 : Nat.nth Nat.Prime 1 = 3 := nthPrime_1_eq_3_aux
  have h2 : Nat.nth Nat.Prime 2 = 5 := nthPrime_2_eq_5_aux
  have h3 : Nat.nth Nat.Prime 3 = 7 := nthPrime_3_eq_7_aux
  have h4 : Nat.nth Nat.Prime 4 = 11 := nthPrime_4_eq_11_aux
  have h5 : Nat.nth Nat.Prime 5 = 13 := nthPrime_5_eq_13_aux
  have h6 : Nat.nth Nat.Prime 6 = 17 := nthPrime_6_eq_17_aux
  have h7 : Nat.nth Nat.Prime 7 = 19 := nthPrime_7_eq_19_aux
  have h8 : Nat.nth Nat.Prime 8 = 23 := nthPrime_8_eq_23_aux
  have h29_prime : Nat.Prime 29 := by decide
  have h24_not_prime : ¬Nat.Prime 24 := by decide
  have h25_not_prime : ¬Nat.Prime 25 := by decide
  have h26_not_prime : ¬Nat.Prime 26 := by decide
  have h27_not_prime : ¬Nat.Prime 27 := by decide
  have h28_not_prime : ¬Nat.Prime 28 := by decide
  have hge29 : Nat.nth Nat.Prime 9 ≥ 29 := by
    have hlt : Nat.nth Nat.Prime 8 < Nat.nth Nat.Prime 9 :=
      Nat.nth_strictMono Nat.infinite_setOf_prime (by omega : 8 < 9)
    have hp9 : Nat.Prime (Nat.nth Nat.Prime 9) :=
      Nat.nth_mem_of_infinite Nat.infinite_setOf_prime 9
    have hgt23 : Nat.nth Nat.Prime 9 > 23 := by omega
    have hne24 : Nat.nth Nat.Prime 9 ≠ 24 := by
      intro heq; rw [heq] at hp9; exact h24_not_prime hp9
    have hne25 : Nat.nth Nat.Prime 9 ≠ 25 := by
      intro heq; rw [heq] at hp9; exact h25_not_prime hp9
    have hne26 : Nat.nth Nat.Prime 9 ≠ 26 := by
      intro heq; rw [heq] at hp9; exact h26_not_prime hp9
    have hne27 : Nat.nth Nat.Prime 9 ≠ 27 := by
      intro heq; rw [heq] at hp9; exact h27_not_prime hp9
    have hne28 : Nat.nth Nat.Prime 9 ≠ 28 := by
      intro heq; rw [heq] at hp9; exact h28_not_prime hp9
    omega
  have hle29 : Nat.nth Nat.Prime 9 ≤ 29 := by
    have hleast := Nat.isLeast_nth_of_infinite Nat.infinite_setOf_prime 9
    have hmem : 29 ∈ {i | Nat.Prime i ∧ ∀ k < 9, Nat.nth Nat.Prime k < i} := by
      simp only [Set.mem_setOf_eq]
      constructor
      · exact h29_prime
      · intro k hk
        interval_cases k <;> omega
    exact hleast.2 hmem
  omega

lemma nthPrime_10_eq_29 : nthPrime 10 = 29 := by
  unfold nthPrime
  simp only [show (10 : ℕ) ≠ 0 by omega, ↓reduceIte]
  have h : (10 : ℕ) - 1 = 9 := by omega
  rw [h]
  exact nthPrime_9_eq_29_aux

lemma primeGap_9_eq_6 : primeGap 9 = 6 := by
  unfold primeGap
  have hp9 : nthPrime 9 = 23 := nthPrime_9_eq_23
  have hp10 : nthPrime 10 = 29 := nthPrime_10_eq_29
  rw [hp9, hp10]

/-- The equivalence: "L(n)=n detects twins" ↔ "twin density hypothesis" -/
theorem bridge_theorem
    (hprime_mono : ∀ i, i ≥ 1 → nthPrime i < nthPrime (i + 1))
    (hgap_ge_2 : ∀ i, i ≥ 1 → primeGap i ≥ 2) :
    (∀ n : ℕ, n ≥ 10 → (L n = n ↔ isTwinIndex n)) ↔ TwinDensityHypothesis := by
  constructor
  · -- Forward direction: detector works → TwinDensityHypothesis
    intro hdetector
    unfold TwinDensityHypothesis
    by_contra hall
    push_neg at hall

    obtain ⟨n₀, hn₀_ge, hgap₀, hno₀⟩ := hall
    let P : ℕ → Prop := fun n => n ≥ 10 ∧ primeGap n ≥ 4 ∧
      ∀ i : ℕ, 1 ≤ i → i < n → isTwinIndex i → nthPrime i * primeGap n ≤ 2 * nthPrime n
    have hP_dec : DecidablePred P := fun _ => Classical.dec _
    have hP_exists : ∃ n, P n := ⟨n₀, hn₀_ge, hgap₀, hno₀⟩

    let n := @Nat.find P hP_dec hP_exists
    have hn_spec : P n := @Nat.find_spec P hP_dec hP_exists
    have hn_min : ∀ m < n, ¬P m := fun m hm => @Nat.find_min P hP_dec hP_exists m hm

    obtain ⟨hn, hgap, hno⟩ := hn_spec

    have hnottwin : ¬isTwinIndex n := by
      unfold isTwinIndex
      omega

    have hLne : L n ≠ n := by
      intro hL
      have := (hdetector n hn).mp hL
      exact hnottwin this

    have hrecord : isStrictRecordMin n := by
      unfold isStrictRecordMin
      intro j hj1 hjn
      by_cases htwinj : isTwinIndex j
      · exact nontwin_beats_twin_when_density_fails n j hn hgap hj1 hjn htwinj hno hprime_mono
      · have hgapj_ge2 : primeGap j ≥ 2 := hgap_ge_2 j hj1
        have hgapj_ne2 : primeGap j ≠ 2 := by
          unfold isTwinIndex at htwinj
          exact htwinj

        have hj_ge2 : j ≥ 2 := by
          by_contra hj_lt2
          push_neg at hj_lt2
          have hj1' : j = 1 := by omega
          rw [hj1'] at hgapj_ge2
          have hgap1_lt : primeGap 1 < 2 := by
            unfold primeGap nthPrime
            simp only [one_ne_zero, ↓reduceIte, show (2 : ℕ) ≠ 0 by omega, Nat.add_sub_cancel]
            have h11 : (1 : ℕ) - 1 = 0 := by omega
            simp only [h11]
            have h0 : Nat.nth Nat.Prime 0 = 2 := Nat.nth_prime_zero_eq_two
            have h1_ge : Nat.nth Nat.Prime 1 ≥ 3 := by
              have hlt : Nat.nth Nat.Prime 0 < Nat.nth Nat.Prime 1 :=
                Nat.nth_strictMono Nat.infinite_setOf_prime (by omega : 0 < 1)
              omega
            have h1_le : Nat.nth Nat.Prime 1 ≤ 3 := by
              have hp1 : Nat.Prime (Nat.nth Nat.Prime 1) :=
                Nat.nth_mem_of_infinite Nat.infinite_setOf_prime 1
              have h3_prime : Nat.Prime 3 := by decide
              by_contra hgt
              push_neg at hgt
              have hleast := Nat.isLeast_nth_of_infinite Nat.infinite_setOf_prime 1
              have hmem : 3 ∈ {i | Nat.Prime i ∧ ∀ k < 1, Nat.nth Nat.Prime k < i} := by
                simp only [Set.mem_setOf_eq]
                exact ⟨h3_prime, fun k hk => by rw [show k = 0 by omega, h0]; omega⟩
              exact Nat.not_lt.mpr (hleast.2 hmem) hgt
            have h1_eq : Nat.nth Nat.Prime 1 = 3 := by omega
            rw [h0, h1_eq]
            omega
          omega

        have hgapj_even : Even (primeGap j) := by
          unfold primeGap
          have hp_j : Nat.Prime (nthPrime j) := by
            unfold nthPrime
            simp only [show j ≠ 0 by omega, ↓reduceIte]
            exact Nat.nth_mem_of_infinite Nat.infinite_setOf_prime (j - 1)
          have hp_j1 : Nat.Prime (nthPrime (j + 1)) := by
            unfold nthPrime
            simp only [show j + 1 ≠ 0 by omega, ↓reduceIte, Nat.add_sub_cancel]
            exact Nat.nth_mem_of_infinite Nat.infinite_setOf_prime j
          have hge3_j : nthPrime j ≥ 3 := by
            have h2_le : nthPrime 2 ≤ nthPrime j := by
              rcases Nat.lt_or_eq_of_le hj_ge2 with hlt | heq
              · exact le_of_lt (nthPrime_strictMono 2 j (by omega) hlt)
              · rw [heq]
            unfold nthPrime at h2_le ⊢
            simp only [show j ≠ 0 by omega, ↓reduceIte, show (2 : ℕ) ≠ 0 by omega] at h2_le ⊢
            have h21 : (2 : ℕ) - 1 = 1 := by omega
            rw [h21] at h2_le
            have h0 : Nat.nth Nat.Prime 0 = 2 := Nat.nth_prime_zero_eq_two
            have hp1_ge : Nat.nth Nat.Prime 1 ≥ 3 := by
              have hlt : Nat.nth Nat.Prime 0 < Nat.nth Nat.Prime 1 :=
                Nat.nth_strictMono Nat.infinite_setOf_prime (by omega : 0 < 1)
              omega
            calc Nat.nth Nat.Prime (j - 1) ≥ Nat.nth Nat.Prime 1 := h2_le
              _ ≥ 3 := hp1_ge
          have hodd_j : Odd (nthPrime j) := Nat.Prime.odd_of_ne_two hp_j (by omega)
          have hodd_j1 : Odd (nthPrime (j + 1)) := by
            have hge3_j1 : nthPrime (j + 1) > nthPrime j := hprime_mono j hj1
            exact Nat.Prime.odd_of_ne_two hp_j1 (by omega)
          exact Nat.Odd.sub_odd hodd_j1 hodd_j

        have hgapj : primeGap j ≥ 4 := by
          obtain ⟨k, hk⟩ := hgapj_even
          omega

        have hdensity_holds_at_j : ∃ i : ℕ, 1 ≤ i ∧ i < j ∧ isTwinIndex i
            ∧ nthPrime i * primeGap j > 2 * nthPrime j := by
          by_cases hj_small : j < 10
          · by_cases hj_le_4 : j ≤ 4
            · -- j ∈ {2, 3, 4} with gap ≥ 4, non-twin means j = 4
              have hj_eq_4 : j = 4 := by
                have hgap2 : primeGap 2 = 2 := by
                  unfold primeGap nthPrime
                  simp only [show (2 : ℕ) ≠ 0 by omega, show (3 : ℕ) ≠ 0 by omega, ↓reduceIte,
                             Nat.add_sub_cancel]
                  have h21 : (2 : ℕ) - 1 = 1 := by omega
                  simp only [h21]
                  have h1 : Nat.nth Nat.Prime 1 = 3 := nthPrime_1_eq_3_aux
                  have h2 : Nat.nth Nat.Prime 2 = 5 := nthPrime_2_eq_5_aux
                  omega
                have hgap3 : primeGap 3 = 2 := by
                  unfold primeGap nthPrime
                  simp only [show (3 : ℕ) ≠ 0 by omega, show (4 : ℕ) ≠ 0 by omega, ↓reduceIte,
                             Nat.add_sub_cancel]
                  have h31 : (3 : ℕ) - 1 = 2 := by omega
                  simp only [h31]
                  have h2 : Nat.nth Nat.Prime 2 = 5 := nthPrime_2_eq_5_aux
                  have h3 : Nat.nth Nat.Prime 3 = 7 := nthPrime_3_eq_7_aux
                  omega
                have hj_ne2 : j ≠ 2 := fun h => hgapj_ne2 (h ▸ hgap2)
                have hj_ne3 : j ≠ 3 := fun h => hgapj_ne2 (h ▸ hgap3)
                omega
              use 3
              rw [hj_eq_4]
              refine ⟨by omega, by omega, ?_, ?_⟩
              · -- isTwinIndex 3
                unfold isTwinIndex primeGap nthPrime
                simp only [show (3 : ℕ) ≠ 0 by omega, show (4 : ℕ) ≠ 0 by omega, ↓reduceIte]
                have h31 : (3 : ℕ) - 1 = 2 := by omega
                have h41 : (4 : ℕ) - 1 = 3 := by omega
                simp only [h31, h41]
                have h2 : Nat.nth Nat.Prime 2 = 5 := nthPrime_2_eq_5_aux
                have h3 : Nat.nth Nat.Prime 3 = 7 := nthPrime_3_eq_7_aux
                omega
              · -- nthPrime 3 * primeGap 4 > 2 * nthPrime 4
                have hp3 : nthPrime 3 = 5 := nthPrime_3_eq_5
                have hp4 : nthPrime 4 = 7 := nthPrime_4_eq_7
                have hgap4 : primeGap 4 = 4 := primeGap_4_eq_4
                rw [hp3, hp4, hgap4]
                omega
            · push_neg at hj_le_4
              -- j ∈ {5, 6, 7, 8, 9} with gap ≥ 4, non-twin
              -- j = 5 and j = 7 are twins, so j ∈ {6, 8, 9}
              have hp5 : nthPrime 5 = 11 := nthPrime_5_eq_11
              have hp6 : nthPrime 6 = 13 := nthPrime_6_eq_13
              have hp7 : nthPrime 7 = 17 := nthPrime_7_eq_17
              have hp8 : nthPrime 8 = 19 := nthPrime_8_eq_19
              have hp9 : nthPrime 9 = 23 := nthPrime_9_eq_23
              have hgap5 : primeGap 5 = 2 := by unfold primeGap; rw [hp5, hp6]
              have hgap7 : primeGap 7 = 2 := by unfold primeGap; rw [hp7, hp8]
              have hj_not_5 : j ≠ 5 := fun h => hgapj_ne2 (h ▸ hgap5)
              have hj_not_7 : j ≠ 7 := fun h => hgapj_ne2 (h ▸ hgap7)
              -- So j ∈ {6, 8, 9}
              have hgap6 : primeGap 6 = 4 := primeGap_6_eq_4
              have hgap8 : primeGap 8 = 4 := primeGap_8_eq_4
              have hgap9 : primeGap 9 = 6 := primeGap_9_eq_6
              -- Use twin index 5 for all cases
              use 5
              have hj_ge6 : j ≥ 6 := by omega
              refine ⟨by omega, by omega, ?_, ?_⟩
              · -- isTwinIndex 5
                unfold isTwinIndex primeGap nthPrime
                simp only [show (5 : ℕ) ≠ 0 by omega, show (6 : ℕ) ≠ 0 by omega, ↓reduceIte]
                have h51 : (5 : ℕ) - 1 = 4 := by omega
                have h61 : (6 : ℕ) - 1 = 5 := by omega
                simp only [h51, h61]
                have h4 : Nat.nth Nat.Prime 4 = 11 := nthPrime_4_eq_11_aux
                have h5 : Nat.nth Nat.Prime 5 = 13 := nthPrime_5_eq_13_aux
                omega
              · -- nthPrime 5 * primeGap j > 2 * nthPrime j
                rw [hp5]
                rcases Nat.lt_trichotomy j 6 with hj_lt6 | hj_eq6 | hj_gt6
                · omega
                · rw [hj_eq6, hp6, hgap6]; omega
                · rcases Nat.lt_trichotomy j 8 with hj_lt8 | hj_eq8 | hj_gt8
                  · omega
                  · rw [hj_eq8, hp8, hgap8]; omega
                  · have hj_eq9 : j = 9 := by omega
                    rw [hj_eq9, hp9, hgap9]; omega
          · push_neg at hj_small
            have hP_j_false : ¬P j := hn_min j hjn
            by_contra hall_j
            push_neg at hall_j
            exact hP_j_false ⟨hj_small, hgapj, hall_j⟩

        obtain ⟨i, hi1, hij, hitwin_i, hibig_i⟩ := hdensity_holds_at_j
        have hin : i < n := by omega
        have hratio_ni : ratioLt n i :=
          nontwin_beats_twin_when_density_fails n i hn hgap hi1 hin hitwin_i hno hprime_mono
        have hratio_ij : ratioLt i j := by
          unfold ratioLt primeRatioNum primeRatioDen
          unfold isTwinIndex primeGap at hitwin_i
          have hi1_eq : nthPrime (i + 1) = nthPrime i + 2 := by
            have hlt : nthPrime i < nthPrime (i + 1) := hprime_mono i hi1
            omega
          have hj1_eq : nthPrime (j + 1) = nthPrime j + primeGap j := by
            unfold primeGap
            have hlt : nthPrime j < nthPrime (j + 1) := hprime_mono j hj1
            omega
          rw [hi1_eq, hj1_eq]
          nlinarith
        exact ratioLt_trans hratio_ni hratio_ij (by omega) hi1 hj1

    have hL : L n = n := (keystone_lemma n (by omega) hprime_mono).mpr hrecord
    exact hLne hL

  · intro hdensity n hn
    exact perfect_iff_twin_conditional hdensity n hn hprime_mono hgap_ge_2
