/-
SortBounds/Instances/ZeroOne.lean

**The 0-1 principle for sorting networks**, and what it buys: a network that sorts
all `0`/`1` inputs sorts *every* input, so a concrete network can be verified by
checking `2 ^ n` inputs instead of `n!` permutations.  Together with
`Instances/Network.lean` (`n! ≤ 2 ^ #comparators`) this makes concrete networks
checkable and keeps the counting bound honest.

Two semantics are used and then identified:

* `ceStep`/`netRun` — the standard one: a comparator replaces its two wires by
  `min` and `max`;
* `runPerm`/`netOut` (`Instances/Network.lean`) — the permutation of wires, used
  for the counting bound.

`netRun_eq_netOut` shows they agree.  The proof of the 0-1 principle is the
classical one: threshold an arbitrary input at a value that separates two
out-of-order outputs; thresholding commutes with every comparator because `min`
and `max` commute with monotone maps (`Monotone.map_min`, `Monotone.map_max`),
hence with the whole network; the thresholded input is 0-1 and still unsorted.
-/
import SortBounds.Instances.Network

namespace SortBounds

variable {n : ℕ} {α : Type*}

/-- One comparator, as `min`/`max` on the two wires it touches. -/
def ceStep [LinearOrder α] (c : Fin n × Fin n) (x : Fin n → α) : Fin n → α :=
  fun k => if k = c.1 then min (x c.1) (x c.2) else if k = c.2 then max (x c.1) (x c.2) else x k

/-- Run a network with `min`/`max` semantics. -/
def netRun [LinearOrder α] (net : Network n) (x : Fin n → α) : Fin n → α :=
  net.foldl (fun acc c => ceStep c acc) x

theorem ceStep_apply_left [LinearOrder α] (c : Fin n × Fin n) (x : Fin n → α) :
    ceStep c x c.1 = min (x c.1) (x c.2) := by
  simp [ceStep]

theorem ceStep_apply_of_ne [LinearOrder α] (c : Fin n × Fin n) (x : Fin n → α) {k : Fin n}
    (h1 : k ≠ c.1) (h2 : k ≠ c.2) : ceStep c x k = x k := by
  simp [ceStep, h1, h2]

theorem ceStep_apply_right [LinearOrder α] (c : Fin n × Fin n) (x : Fin n → α) (h : c.2 ≠ c.1) :
    ceStep c x c.2 = max (x c.1) (x c.2) := by
  simp [ceStep, h]

/-- `ceStep` on an array of the form `fun k => x (σ k)`: it either leaves the
permutation alone (values already in order) or swaps the two wires. -/
theorem ceStep_comp [LinearOrder α] (c : Fin n × Fin n) (x : Fin n → α)
    (σ : Equiv.Perm (Fin n)) :
    ceStep c (fun k => x (σ k)) =
      if x (σ c.1) ≤ x (σ c.2) then (fun k => x (σ k))
        else (fun k => x ((σ * Equiv.swap c.1 c.2) k)) := by
  by_cases hlt : x (σ c.1) ≤ x (σ c.2)
  · rw [ite_eq_left hlt]
    funext k
    by_cases h1 : k = c.1
    · subst h1; rw [ceStep_apply_left]; simp [hlt]
    · by_cases h2 : k = c.2
      · subst h2; rw [ceStep_apply_right c _ (by omega)]; simp [hlt]
      · rw [ceStep_apply_of_ne c _ h1 h2]
  · rw [ite_eq_right hlt]
    have hlt' : x (σ c.2) < x (σ c.1) := lt_of_le_of_ne (le_of_lt (lt_of_not_ge hlt)) (by
      intro hcon; exact hlt (le_of_eq hcon.symm))
    funext k
    by_cases h1 : k = c.1
    · subst h1
      rw [ceStep_apply_left]
      simp only [min_eq_right (le_of_lt hlt'), Equiv.Perm.mul_apply, Equiv.swap_apply_left]
    · by_cases h2 : k = c.2
      · subst h2
        rw [ceStep_apply_right c _ (by omega)]
        simp only [max_eq_left (le_of_lt hlt'), Equiv.Perm.mul_apply, Equiv.swap_apply_right]
      · rw [ceStep_apply_of_ne c _ h1 h2]
        simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne h1 h2]

/-- **The two semantics agree.**  Running the network with `min`/`max` produces the
input permuted by the wire permutation of `runPerm`. -/
theorem foldl_ceStep_eq [LinearOrder α] (net : Network n) (x : Fin n → α)
    (σ : Equiv.Perm (Fin n)) :
    net.foldl (fun acc c => ceStep c acc) (fun k => x (σ k)) =
      fun k => x (net.foldl
        (fun σ c => if x (σ c.1) ≤ x (σ c.2) then σ else σ * Equiv.swap c.1 c.2) σ k) := by
  induction net generalizing σ with
  | nil => rfl
  | cons c rest ih =>
    rw [List.foldl_cons, List.foldl_cons, ceStep_comp c x σ]
    by_cases h : x (σ c.1) ≤ x (σ c.2)
    · rw [ite_eq_left h, ite_eq_left h]
      exact ih σ
    · rw [ite_eq_right h, ite_eq_right h]
      exact ih (σ * Equiv.swap c.1 c.2)

theorem netRun_eq_netOut [LinearOrder α] (net : Network n) (x : Fin n → α) :
    netRun net x = netOut net x :=
  foldl_ceStep_eq net x 1

/-! ### Thresholding commutes with the network -/

/-- Thresholding commutes with a single comparator. -/
theorem ceStep_map {β : Type*} [LinearOrder β] (ij : Fin n × Fin n) (g : ℕ → β)
    (hg : Monotone g) (x : Fin n → ℕ) :
    ceStep ij (fun k => g (x k)) = fun k => g (ceStep ij x k) := by
  obtain ⟨i, j⟩ := ij
  funext k
  by_cases hij : i = j
  · subst hij
    by_cases hk : k = i
    · subst hk; simp [ceStep]
    · simp [ceStep, hk]
  · by_cases h1 : k = i
    · subst h1
      simp [ceStep, hg.map_min]
    · by_cases h2 : k = j
      · subst h2
        simp [ceStep, h1, hg.map_max]
      · simp [ceStep, h1, h2]

/-- Thresholding commutes with the whole network. -/
theorem map_netRun {β : Type*} [LinearOrder β] (net : Network n) (g : ℕ → β)
    (hg : Monotone g) (x : Fin n → ℕ) :
    (fun k => g (netRun net x k)) = netRun net (fun k => g (x k)) := by
  have key : ∀ (net : Network n) (acc : Fin n → ℕ),
      (fun k => g (net.foldl (fun a c => ceStep c a) acc k))
        = net.foldl (fun a c => ceStep c a) (fun k => g (acc k)) := by
    intro net
    induction net with
    | nil => intro acc; rfl
    | cons c rest ih =>
      intro acc
      rw [List.foldl_cons, List.foldl_cons]
      calc (fun k => g ((rest.foldl (fun a c => ceStep c a) (ceStep c acc)) k))
          = rest.foldl (fun a c => ceStep c a) (fun k => g (ceStep c acc k)) := ih (ceStep c acc)
        _ = rest.foldl (fun a c => ceStep c a) (ceStep c (fun k => g (acc k))) := by
              rw [← ceStep_map c g hg acc]
  exact key net x

/-- The 0-1 threshold map: `0` at or below `c`, `1` above.  Landing in `Fin 2`
(not `ℕ`) is what makes the 0-1 hypothesis decidable, hence a concrete network
checkable by `decide`. -/
def thresh (c v : ℕ) : Fin 2 := if v ≤ c then 0 else 1

theorem thresh_monotone (c : ℕ) : Monotone (thresh c) := by
  intro a b hab
  unfold thresh
  by_cases ha : a ≤ c
  · rw [ite_eq_left ha]; exact Fin.zero_le _
  · rw [ite_eq_right ha]
    have hb : ¬ b ≤ c := fun h => ha (le_trans hab h)
    rw [ite_eq_right hb]

/-! ### The 0-1 principle -/

/-- **0-1 principle.**  A comparator network that sorts every `0`/`1` input sorts
every input.  The hypothesis is over `Fin n → Fin 2`, a *finite* type, so a
concrete network can be verified by `decide`. -/
theorem sortsAll_of_sorts_zeroOne (net : Network n)
    (h : ∀ y : Fin n → Fin 2, Monotone (netRun net y)) : SortsAll net := by
  intro x
  rw [← netRun_eq_netOut]
  by_contra hbad
  simp only [Monotone] at hbad
  push Not at hbad
  obtain ⟨a, b, hab, hlt⟩ := hbad
  -- threshold the input at the value of the smaller out-of-order output
  set g : ℕ → Fin 2 := fun v => if v ≤ netRun net x b then 0 else 1 with hg
  have hgmono : Monotone g := fun u v huv => thresh_monotone (netRun net x b) huv
  have hcomm : netRun net (fun k => g (x k)) = fun k => g (netRun net x k) :=
    (map_netRun net g hgmono x).symm
  have hmono := h (fun k => g (x k)) hab
  rw [hcomm] at hmono
  change g (netRun net x a) ≤ g (netRun net x b) at hmono
  have hb : g (netRun net x b) = 0 := by simp [hg]
  have ha : g (netRun net x a) = 1 := by
    simp only [hg, ite_eq_right (not_le.mpr hlt)]
  rw [ha, hb] at hmono
  exact absurd hmono (by decide)

/-- **Sorting networks can be verified on `2 ^ n` inputs.**  A network that sorts
every `0`/`1` input has at least `log₂(n!)` comparators. -/
theorem factorial_le_two_pow_length_of_sorts_zeroOne (net : Network n)
    (h : ∀ y : Fin n → Fin 2, Monotone (netRun net y)) :
    Nat.factorial n ≤ 2 ^ net.length :=
  factorial_le_two_pow_length_of_sortsAll (sortsAll_of_sorts_zeroOne net h)

/-- The three-wire network `(0,1), (1,2), (0,1)` sorts every 0/1 input: a
`decide` over `2 ^ 3 = 8` inputs, exactly the win the 0-1 principle provides. -/
theorem sorts_zeroOne_three_wire : ∀ y : Fin 3 → Fin 2, Monotone (netRun [(0, 1), (1, 2), (0, 1)] y) := by
  decide

/-- Hence `3! = 6 ≤ 2 ^ 3`: three comparators suffice for three wires. -/
theorem three_wire_bound :
    Nat.factorial 3 ≤ 2 ^ ([(0, 1), (1, 2), (0, 1)] : Network 3).length :=
  factorial_le_two_pow_length_of_sorts_zeroOne _ sorts_zeroOne_three_wire

end SortBounds
