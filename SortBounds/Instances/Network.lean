/-
SortBounds/Instances/Network.lean

**Do sorting networks escape the `n log n` bound?**  No — they are comparison
algorithms, just *oblivious* ones: a network on `n` wires is a fixed list of
comparators, and running it induces a binary decision tree of depth equal to the
number of comparators.  So the counting argument applies with `b = 2` and gives

> `n! ≤ 2 ^ (number of comparators)`.

What a network buys is *depth*, not work: `O(log n)` depth (Ajtai–Komlós–
Szemerédi) with `Θ(n log n)` comparators, which is exactly the counting bound.
Formalised here without any decision-tree machinery: the permutation of wires
realised by the network is one of at most `2 ^ length` products of "swap or don't
swap" choices, so distinct inputs must induce distinct permutations.

This is the same `2 ^ k` counting as `SortBounds.Core.Branching`, specialised to
the permutation-of-wires encoding (so it does not need the general word lemma),
and it is where the radix-sort escape visibly *does not* apply: radix sort is not
a network of comparisons at all.
-/
import SortBounds.Comparison.Basic

namespace SortBounds

variable {n : ℕ} {α : Type*}

/-- A comparator network on `n` wires: a list of pairs of wires to compare. -/
abbrev Network (n : ℕ) := List (Fin n × Fin n)

/-- The permutation of wires realised by the network on input `x`: output position
`k` holds the input value from position `runPerm net x k`.  Reading the network as
a fold, a comparator either leaves the realised permutation alone or composes it
with a transposition of the two wires. -/
def runPerm [LinearOrder α] (net : Network n) (x : Fin n → α) : Equiv.Perm (Fin n) :=
  net.foldl (fun σ c => if x (σ c.1) ≤ x (σ c.2) then σ else σ * Equiv.swap c.1 c.2) 1

/-- The array produced by running the network on `x`. -/
def netOut [LinearOrder α] (net : Network n) (x : Fin n → α) : Fin n → α :=
  fun k => x (runPerm net x k)

/-- One comparator applied to a set of reachable permutations: keep them all, and
add the transposed variants. -/
def step (s : Finset (Equiv.Perm (Fin n))) (c : Fin n × Fin n) : Finset (Equiv.Perm (Fin n)) :=
  s ∪ s.image (fun σ => σ * Equiv.swap c.1 c.2)

/-- The set of permutations the network *could* realise, over all possible
swap/no-swap outcomes: start from the identity and apply `step` comparator by
comparator, in the order the network runs. -/
def reachPerms (net : Network n) : Finset (Equiv.Perm (Fin n)) :=
  net.foldl step {1}

/-- One comparator at most doubles the set of reachable permutations. -/
theorem card_step_le (s : Finset (Equiv.Perm (Fin n))) (c : Fin n × Fin n) :
    (step s c).card ≤ 2 * s.card := by
  calc (step s c).card ≤ s.card + (s.image (fun σ => σ * Equiv.swap c.1 c.2)).card :=
        Finset.card_union_le _ _
    _ ≤ s.card + s.card := Nat.add_le_add_left Finset.card_image_le _
    _ = 2 * s.card := by ring

/-- `k` comparators leave at most `2 ^ k` reachable permutations. -/
theorem card_foldl_step_le (net : Network n) (s : Finset (Equiv.Perm (Fin n))) :
    (net.foldl step s).card ≤ s.card * 2 ^ net.length := by
  induction net generalizing s with
  | nil => simp
  | cons c rest ih =>
    rw [List.foldl_cons, List.length_cons]
    calc (rest.foldl step (step s c)).card ≤ (step s c).card * 2 ^ rest.length := ih (step s c)
      _ ≤ (2 * s.card) * 2 ^ rest.length := Nat.mul_le_mul_right _ (card_step_le s c)
      _ = s.card * 2 ^ (rest.length + 1) := by ring

theorem card_reachPerms_le (net : Network n) : (reachPerms net).card ≤ 2 ^ net.length := by
  have := card_foldl_step_le net {1}
  simpa [reachPerms] using this

/-- The realised permutation is always reachable. -/
theorem runPerm_mem_reachPerms [LinearOrder α] (net : Network n) (x : Fin n → α) :
    runPerm net x ∈ reachPerms net := by
  have key : ∀ (net : Network n) (s : Finset (Equiv.Perm (Fin n))) (σ : Equiv.Perm (Fin n)),
      σ ∈ s → net.foldl (fun σ c => if x (σ c.1) ≤ x (σ c.2) then σ else σ * Equiv.swap c.1 c.2) σ
        ∈ net.foldl step s := by
    intro net
    induction net with
    | nil => intro s σ hσ; exact hσ
    | cons c rest ih =>
      intro s σ hσ
      simp only [List.foldl_cons]
      apply ih
      by_cases hlt : x (σ c.1) ≤ x (σ c.2)
      · rw [ite_eq_left hlt]
        exact Finset.mem_union_left _ hσ
      · rw [ite_eq_right hlt]
        exact Finset.mem_union_right _ (Finset.mem_image.2 ⟨σ, hσ, rfl⟩)
  exact key net {1} 1 (by simp)

/-- The standard specification of a sorting network: whatever the input values
(ties included), the output is nondecreasing. -/
def SortsAll (net : Network n) : Prop :=
  ∀ x : Fin n → ℕ, Monotone (netOut net x)

/-- A sorting network sorts every input with pairwise distinct values. -/
theorem sorts_of_sortsAll {net : Network n} (h : SortsAll net) :
    ∀ x : Fin n → ℕ, Function.Injective x → Sorts x (runPerm net x) := by
  intro x hx
  have hmono : Monotone (netOut net x) := h x
  have hout : netOut net x = fun k => x (runPerm net x k) := rfl
  rw [hout] at hmono
  exact hmono.strictMono_of_injective
    (fun a b hab => (runPerm net x).injective (hx hab))

/-- **A sorting network with `k` comparators needs `k ≥ log₂(n!)`.**
Networks do not beat the comparison bound in *comparator count*; they only win on
depth, because comparators at different levels run in parallel. -/
theorem factorial_le_two_pow_length {net : Network n}
    (h : ∀ x : Fin n → ℕ, Function.Injective x → Sorts x (runPerm net x)) :
    Nat.factorial n ≤ 2 ^ net.length := by
  have hinj : Function.Injective (fun p : Equiv.Perm (Fin n) => runPerm net (xOfPerm p)) := by
    intro p q hpq
    have hpq' : runPerm net (xOfPerm p) = runPerm net (xOfPerm q) := hpq
    have hp : Sorts (xOfPerm p) (runPerm net (xOfPerm p)) := h _ (xOfPerm_injective p)
    have hq : Sorts (xOfPerm q) (runPerm net (xOfPerm q)) := h _ (xOfPerm_injective q)
    rw [← hpq'] at hq
    have h1 : runPerm net (xOfPerm p) = p :=
      Sorts.unique (xOfPerm_injective p) hp (xOfPerm_sorts p)
    have h2 : runPerm net (xOfPerm p) = q :=
      Sorts.unique (xOfPerm_injective q) hq (xOfPerm_sorts q)
    exact h1.symm.trans h2
  calc Nat.factorial n = (Finset.univ : Finset (Equiv.Perm (Fin n))).card := by
        rw [Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
    _ = (Finset.univ.image (fun p : Equiv.Perm (Fin n) => runPerm net (xOfPerm p))).card :=
        (Finset.card_image_of_injective _ hinj).symm
    _ ≤ (reachPerms net).card := by
        apply Finset.card_le_card
        intro σ hσ
        obtain ⟨p, -, rfl⟩ := Finset.mem_image.1 hσ
        exact runPerm_mem_reachPerms net (xOfPerm p)
    _ ≤ 2 ^ net.length := card_reachPerms_le net

/-- The same statement for a network specified the standard way. -/
theorem factorial_le_two_pow_length_of_sortsAll {net : Network n} (h : SortsAll net) :
    Nat.factorial n ≤ 2 ^ net.length :=
  factorial_le_two_pow_length (sorts_of_sortsAll h)

/-- Logarithmic form: `log₂(n!) ≤ number of comparators`. -/
theorem logb_factorial_le_length_of_sortsAll {net : Network n} (h : SortsAll net) :
    Real.logb 2 (Nat.factorial n) ≤ (net.length : ℝ) := by
  have hnat := factorial_le_two_pow_length_of_sortsAll h
  have hcast : (Nat.factorial n : ℝ) ≤ (2 : ℝ) ^ net.length := by exact_mod_cast hnat
  have hpos : (0 : ℝ) < (Nat.factorial n : ℝ) := by exact_mod_cast Nat.factorial_pos n
  rw [Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ) < 2) hpos]
  simpa using hcast

/-! ### Non-vacuity: the one-comparator network on two wires really sorts -/

theorem sortsAll_two_wire : SortsAll (n := 2) [(0, 1)] := by
  intro x
  have hrun : runPerm [(0, 1)] x = if x 0 ≤ x 1 then 1 else Equiv.swap 0 1 := by
    simp [runPerm, List.foldl_cons, List.foldl_nil]
  have hout : netOut [(0, 1)] x = if x 0 ≤ x 1 then x else fun k => x (Equiv.swap 0 1 k) := by
    funext k
    simp only [netOut, hrun]
    split_ifs <;> rfl
  intro a b hab
  rw [hout]
  by_cases h : x 0 ≤ x 1
  · rw [ite_eq_left h]
    rcases eq_or_lt_of_le hab with h' | h'
    · rw [h']
    · have ha : a = 0 := by omega
      have hb : b = 1 := by omega
      simpa [ha, hb] using h
  · rw [ite_eq_right h]
    have hle : x 1 ≤ x 0 := by omega
    rcases eq_or_lt_of_le hab with h' | h'
    · rw [h']
    · have ha : a = 0 := by omega
      have hb : b = 1 := by omega
      subst ha; subst hb
      simpa using hle

/-- `2! = 2 ≤ 2^1`: the bound is attained by the one-comparator network. -/
theorem two_wire_bound : Nat.factorial 2 ≤ 2 ^ ([(0, 1)] : Network 2).length :=
  factorial_le_two_pow_length_of_sortsAll sortsAll_two_wire

end SortBounds
