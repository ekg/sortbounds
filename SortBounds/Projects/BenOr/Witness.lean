/-
SortBounds/Projects/BenOr/Witness.lean

**The semantics is not vacuous.**

`SortBounds.Projects.BenOr.Bound` states Ben-Or's bound as
`t.degreeLe d → t.decidesReal S → c * log (#components of S) ≤ height t`.  Such a
statement is only worth proving if its hypotheses can both hold *and* leave room
for a bound: a `decidesReal` that no tree satisfies would make every one of those
implications vacuously true.

This file exhibits the witnesses.

* `halfLineTree_decidesReal` — the contract's one-test tree decides the half-line
  in the *real* semantics too (the rational witness `halfLineTree_decides` is in
  `Basic.lean`).
* `exists_decidesReal_distinct` — **element distinctness is decided by a tree of
  degree `n * (n - 1)`**: one test, the polynomial `-(∏ p, (x p.1 - x p.2) ^ 2)`,
  is negative exactly on the distinct points.  This is the witness that the lane's
  `decidesReal (distinctSet n)` hypothesis is satisfiable, and it is also why the
  degree bound in `ADT.degreeLe` is not decoration: with `d = n * (n - 1)` the
  height drops to `1`, so the *content* of Ben-Or's bound lives entirely in the
  dependence of the constant on the fixed degree `d`.

The sign argument is carried out over an arbitrary linear ordered field `K`, so it
serves both semantics of the lane: `K = ℝ` with `f = algebraMap ℚ ℝ` is
`ADT.decidesReal`, and `K = ℚ` with `f = RingHom.id ℚ` is `ADT.decides`.  Hence
`distinctnessTree_decides` (rational semantics) comes for free; the
`∏ (x i - x j) ^ 2 ≥ 0` and `= 0 ↔ collapse` facts used are
`Finset.prod_nonneg` and `Finset.prod_eq_zero_iff`.

No `sorry`, no `axiom`.
-/
import Mathlib
import SortBounds.Projects.BenOr.Basic
import SortBounds.Projects.BenOr.Components

namespace SortBounds.Projects.BenOr

/-! ### The distinctness polynomial and its degree -/

/-- The index set of coordinate pairs `i < j`: one factor per unordered pair.
`Finset.card_product_filter_lt` counts it as `n.choose 2`. -/
def distinctPairs (n : ℕ) : Finset (Fin n × Fin n) :=
  Finset.univ.filter (fun p => p.1 < p.2)

theorem card_distinctPairs (n : ℕ) : (distinctPairs n).card = n.choose 2 := by
  rw [distinctPairs, ← Finset.univ_product_univ, Finset.card_product_filter_lt,
    Finset.card_univ, Fintype.card_fin]

/-- Twice the number of unordered pairs is `n * (n - 1)`, so `n.choose 2` pairs of
squares have total degree at most `n * (n - 1)`.  (Proved by induction on `n`
rather than from `n.choose 2 = n * (n - 1) / 2`, to stay out of `ℕ`-division.) -/
theorem two_mul_choose_two_succ (n : ℕ) : 2 * (n + 1).choose 2 = (n + 1) * n := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [Nat.choose_succ_succ, Nat.mul_add, ih, Nat.choose_one_right]
    ring

theorem two_mul_choose_two (n : ℕ) : 2 * n.choose 2 = n * (n - 1) := by
  cases n with
  | zero => simp
  | succ m => simpa using two_mul_choose_two_succ m

/-- The test polynomial of the distinctness tree:
`-(∏ p ∈ distinctPairs n, (X p.1 - X p.2) ^ 2)`.  The minus sign is dictated by
`ADT.run`/`ADT.runReal`, which take the *left* branch on a negative value. -/
noncomputable def distinctnessPoly (n : ℕ) : MvPolynomial (Fin n) ℚ :=
  -(∏ p ∈ distinctPairs n, (MvPolynomial.X p.1 - MvPolynomial.X p.2) ^ 2)

/-- Each squared difference is a total-degree-`2` polynomial
(`totalDegree` of `X i - X j` is `max 1 1`). -/
theorem totalDegree_pair_sq_le (n : ℕ) (p : Fin n × Fin n) :
    ((MvPolynomial.X p.1 - MvPolynomial.X p.2 : MvPolynomial (Fin n) ℚ) ^ 2).totalDegree ≤ 2 := by
  have hsub : (MvPolynomial.X p.1 - MvPolynomial.X p.2 : MvPolynomial (Fin n) ℚ).totalDegree
      ≤ 1 := by
    have := MvPolynomial.totalDegree_sub (MvPolynomial.X p.1 : MvPolynomial (Fin n) ℚ)
      (MvPolynomial.X p.2 : MvPolynomial (Fin n) ℚ)
    simpa using this
  calc ((MvPolynomial.X p.1 - MvPolynomial.X p.2 : MvPolynomial (Fin n) ℚ) ^ 2).totalDegree
      ≤ 2 * (MvPolynomial.X p.1 - MvPolynomial.X p.2 : MvPolynomial (Fin n) ℚ).totalDegree :=
        MvPolynomial.totalDegree_pow
          (MvPolynomial.X p.1 - MvPolynomial.X p.2 : MvPolynomial (Fin n) ℚ) 2
    _ ≤ 2 * 1 := Nat.mul_le_mul_left 2 hsub
    _ = 2 := by norm_num

/-- **The degree of the distinctness test**: at most one per ordered pair of
distinct coordinates, i.e. `n * (n - 1)`.  Exact, not slack: the product of `s`
squares has total degree `2 * s` and there are `n.choose 2` pairs. -/
theorem totalDegree_distinctnessPoly_le (n : ℕ) :
    (distinctnessPoly n).totalDegree ≤ n * (n - 1) := by
  have h1 : (distinctnessPoly n).totalDegree
      ≤ ∑ p ∈ distinctPairs n,
          ((MvPolynomial.X p.1 - MvPolynomial.X p.2 : MvPolynomial (Fin n) ℚ) ^ 2).totalDegree := by
    rw [distinctnessPoly, MvPolynomial.totalDegree_neg]
    exact MvPolynomial.totalDegree_finsetProd _ _
  have h2 : ∑ p ∈ distinctPairs n,
        ((MvPolynomial.X p.1 - MvPolynomial.X p.2 : MvPolynomial (Fin n) ℚ) ^ 2).totalDegree
      ≤ ∑ _p ∈ distinctPairs n, 2 := Finset.sum_le_sum (fun p _ => totalDegree_pair_sq_le n p)
  have h3 : ∑ _p ∈ distinctPairs n, (2 : ℕ) = 2 * (distinctPairs n).card := by
    rw [Finset.sum_const, smul_eq_mul, mul_comm]
  have h4 : 2 * (distinctPairs n).card = n * (n - 1) := by
    rw [card_distinctPairs, two_mul_choose_two]
  omega

/-! ### The sign argument -/

/-- `eval₂` of the distinctness polynomial is minus the product of the squared
coordinate differences. -/
theorem eval₂_distinctnessPoly {K : Type*} [CommRing K] (f : ℚ →+* K)
    (x : Fin n → K) :
    MvPolynomial.eval₂ f x (distinctnessPoly n)
      = -(∏ p ∈ distinctPairs n, (x p.1 - x p.2) ^ 2) := by
  simp [distinctnessPoly]

/-- A product of squares is nonnegative. -/
theorem prod_sq_nonneg {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (x : Fin n → K) :
    0 ≤ ∏ p ∈ distinctPairs n, (x p.1 - x p.2) ^ 2 :=
  Finset.prod_nonneg fun _ _ => sq_nonneg _

/-- A product of squares vanishes exactly when some coordinate pair collapses. -/
theorem prod_sq_eq_zero_iff {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (x : Fin n → K) :
    ∏ p ∈ distinctPairs n, (x p.1 - x p.2) ^ 2 = 0 ↔ ∃ p ∈ distinctPairs n, x p.1 = x p.2 := by
  rw [Finset.prod_eq_zero_iff]
  exact exists_congr fun _ => and_congr_right fun _ => by
    rw [pow_two, mul_self_eq_zero, sub_eq_zero]

/-- `x` is injective exactly when no pair `i < j` of coordinates collapses: the
`<`-filter on pairs loses nothing, because a collision of `i ≠ j` is a collision
of `min i j < max i j`. -/
theorem injective_iff_pairs (x : Fin n → K) :
    Function.Injective x ↔ ∀ p ∈ distinctPairs n, x p.1 ≠ x p.2 := by
  constructor
  · intro hx p hp
    have hlt : p.1 < p.2 := by simpa [distinctPairs] using hp
    exact fun h => ne_of_lt hlt (hx h)
  · intro h i j hij
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact h (i, j) (by simp [distinctPairs, hlt]) hij
    · exact h (j, i) (by simp [distinctPairs, hlt]) hij.symm

/-- **The sign lemma.**  The distinctness test is negative exactly on the injective
points, over any linear ordered field `K`: the product of squares is `≥ 0` and
vanishes only at a collision, so `-∏ (x i - x j) ^ 2 < 0` says "no collision". -/
theorem distinctnessPoly_eval₂_neg_iff {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (f : ℚ →+* K) (x : Fin n → K) :
    MvPolynomial.eval₂ f x (distinctnessPoly n) < 0 ↔ Function.Injective x := by
  have hnn : 0 ≤ ∏ p ∈ distinctPairs n, (x p.1 - x p.2) ^ 2 := prod_sq_nonneg x
  have hzero : ∏ p ∈ distinctPairs n, (x p.1 - x p.2) ^ 2 = 0
      ↔ ∃ p ∈ distinctPairs n, x p.1 = x p.2 := prod_sq_eq_zero_iff x
  rw [eval₂_distinctnessPoly, injective_iff_pairs]
  constructor
  · intro h p hp hpx
    rw [hzero.mpr ⟨p, hp, hpx⟩] at h
    simp at h
  · intro h
    have hne : ∏ p ∈ distinctPairs n, (x p.1 - x p.2) ^ 2 ≠ 0 := by
      intro hz
      obtain ⟨p, hp, hpx⟩ := hzero.mp hz
      exact h p hp hpx
    have hpos : 0 < ∏ p ∈ distinctPairs n, (x p.1 - x p.2) ^ 2 := lt_of_le_of_ne hnn (Ne.symm hne)
    linarith

/-! ### The witnesses -/

/-- The one-test distinctness tree: left (`true`) on a negative test value,
i.e. exactly on the distinct inputs. -/
noncomputable def distinctnessTree (n : ℕ) : ADT n :=
  .node (distinctnessPoly n) (.leaf true) (.leaf false)

/-- The distinctness tree has degree `n * (n - 1)`. -/
theorem distinctnessTree_degreeLe (n : ℕ) : (distinctnessTree n).degreeLe (n * (n - 1)) :=
  ⟨totalDegree_distinctnessPoly_le n, trivial, trivial⟩

/-- The distinctness tree decides element distinctness in the real semantics. -/
theorem distinctnessTree_decidesReal (n : ℕ) :
    (distinctnessTree n).decidesReal (distinctSet n) := by
  intro x
  show (if MvPolynomial.eval₂ (algebraMap ℚ ℝ) x (distinctnessPoly n) < 0 then true else false) = true
      ↔ Function.Injective x
  rw [← distinctnessPoly_eval₂_neg_iff (algebraMap ℚ ℝ) x]
  by_cases h : MvPolynomial.eval₂ (algebraMap ℚ ℝ) x (distinctnessPoly n) < 0 <;> simp [h]

/-- The distinctness tree decides element distinctness in the *rational* semantics
as well (`ADT.decides`, evaluated by `ADT.run`). -/
theorem distinctnessTree_decides (n : ℕ) :
    (distinctnessTree n).decides {x : Fin n → ℚ | Function.Injective x} := by
  intro x
  show (if MvPolynomial.eval x (distinctnessPoly n) < 0 then true else false) = true
      ↔ Function.Injective x
  rw [← distinctnessPoly_eval₂_neg_iff (RingHom.id ℚ) x]
  by_cases h : MvPolynomial.eval x (distinctnessPoly n) < 0 <;> simp [h]

/-- **`decidesReal (distinctSet n)` is satisfiable at every `n`** — so no statement
in `SortBounds.Projects.BenOr.Bound` is vacuous for want of a tree deciding
distinctness.  The tree has height `1`; only the *degree* `n * (n - 1)` is large,
which is why Ben-Or's bound cannot be improved by dropping the degree hypothesis. -/
theorem exists_decidesReal_distinct (n : ℕ) :
    ∃ t : ADT n, t.degreeLe (n * (n - 1)) ∧ t.decidesReal (distinctSet n) :=
  ⟨distinctnessTree n, distinctnessTree_degreeLe n, distinctnessTree_decidesReal n⟩

/-- **The half-line witness in the real semantics**: the contract's one-test tree
`halfLineTree` decides `{x | 0 ≤ x 0}` at real points too.  Together with
`halfLineTree_decides` (`Basic.lean`) this makes both semantics of the model
non-vacuous. -/
theorem halfLineTree_decidesReal :
    halfLineTree.decidesReal {x : Fin 1 → ℝ | 0 ≤ x 0} := by
  intro x
  show (if MvPolynomial.eval₂ (algebraMap ℚ ℝ) x (MvPolynomial.X 0) < 0 then false else true) = true
      ↔ 0 ≤ x 0
  rw [MvPolynomial.eval₂_X]
  by_cases h : x 0 < 0
  · rw [ite_eq_left h]
    simp only [Bool.false_eq_true, false_iff]
    linarith
  · rw [ite_eq_right h]
    simp only [true_iff]
    linarith

end SortBounds.Projects.BenOr
