/-
SortBounds/Projects/DeBruijn/DeBruijn.lean

**The separation `γ ≥ 2^k/k` for binary de Bruijn words** (`docs/research/gamma-vs-gamma2.md`).

A binary de Bruijn word `B_k` of order `k` has length `2^k + k - 1` and contains every binary
`k`-gram.  Two counting facts then pin its substring complexity `δ`:

* every `i`-gram with `i ≤ k` occurs too (pad it on the right to a `k`-gram), so `d_i = 2^i`
  for `1 ≤ i ≤ k` — `card_distinctFactors_of_coversAllWords` together with
  `coversAllWords_mono`;
* `2^i/i` is nondecreasing for `i ≥ 1` (`ratio_mono`), and for `i > k` the number of
  *positions* `s.length - i + 1 = 2^k + k - i` keeps `d_i/i` below `2^k/k`
  (`card_distinctFactors_le`, `ratio_le_of_lt`),

so `δ(B_k) = 2^k/k` (`deltaQ_isDeBruijn`).  With `δ ≤ γ` — Kempa–Kociumaka–Prezza Lemma II.4,
machine-checked as `Repetitiveness.deltaQ_le_minAttractorSize` — that is `γ(B_k) ≥ 2^k/k`
(`gamma_ge_of_isDeBruijn`), the bound that kills the hope that `γ` is within a constant factor
of `γ₂` (the other factor, `γ₂(B_k) ≤ 4`, is *not* proved here — see the note at the end).

**What is deliberately not here.**  Existence of de Bruijn words for every `k` (de Bruijn 1946,
FKM) is not formalized: it is a *hypothesis* of the two main theorems, and the witnesses
`isDeBruijn_two`/`isDeBruijn_three` show the hypothesis is inhabited at `k = 2, 3`.  `δ` is
KNP's rational substring complexity `deltaQ` (not the floored `substringComplexity`), because
the interesting value `2^k/k` is rarely an integer.
-/
import Mathlib
import SortBounds.Projects.Repetitiveness.Attractor

namespace SortBounds.Projects.DeBruijn

open SortBounds
open SortBounds.Projects.Repetitiveness

variable {s : List Bool}

/-! ### M0: the counting core -/

/-- Every binary word of length `k` occurs as a factor of `s`. -/
def CoversAllWords (s : List Bool) (k : ℕ) : Prop :=
  ∀ w : List Bool, w.length = k → w ∈ distinctFactors s k

/-- A de Bruijn word of order `k`: length `2^k + k - 1` and every `k`-gram occurs.  (A word
of that length has exactly `2^k` windows, so "all `2^k` words occur" says each occurs exactly
once — the length condition makes this the usual definition, not a weakening of it.) -/
def IsDeBruijn (s : List Bool) (k : ℕ) : Prop :=
  s.length = 2 ^ k + k - 1 ∧ CoversAllWords s k

/-- Every list of length `i` is `List.ofFn` of some `Fin i → Bool`-tuple, so quantifying over
words of a fixed length is a quantification over the finite type `Fin i → Bool`. -/
theorem exists_ofFn_eq {f : List Bool} {i : ℕ} (h : f.length = i) :
    ∃ w : Fin i → Bool, List.ofFn w = f := by
  subst h
  exact ⟨List.get f, List.ofFn_get f⟩

/-- `CoversAllWords` in the finite form used for the `decide` checks: enumerate the `2^k`
words as `Fin k → Bool`. -/
theorem coversAllWords_iff_fin {k : ℕ} :
    CoversAllWords s k ↔ ∀ w : Fin k → Bool, List.ofFn w ∈ distinctFactors s k := by
  constructor
  · intro h w
    exact h _ List.length_ofFn
  · rintro h w hw
    obtain ⟨v, rfl⟩ := exists_ofFn_eq hw
    exact h v

/-- **The counting core**: if every binary word of length `i` occurs in `s`, then `s` has
exactly `2^i` distinct factors of length `i`.  (`≥`: the `2^i` words of length `i` are
distinct and all occur.  `≤`: every factor of length `i` *is* a word of length `i`.) -/
theorem card_distinctFactors_of_coversAllWords {i : ℕ} (h : CoversAllWords s i) :
    (distinctFactors s i).card = 2 ^ i := by
  have himage : (Finset.univ.image (fun w : Fin i → Bool => List.ofFn w)).card = 2 ^ i := by
    rw [Finset.card_image_of_injective _ List.ofFn_injective, Finset.card_univ]
    simp
  refine le_antisymm ?_ ?_
  · calc (distinctFactors s i).card
        ≤ (Finset.univ.image (fun w : Fin i → Bool => List.ofFn w)).card := by
          apply Finset.card_le_card
          intro f hf
          obtain ⟨p, hpn, rfl⟩ := mem_distinctFactors.mp hf
          have hlen : ((s.drop p).take i).length = i := by
            rw [List.length_take, List.length_drop]
            omega
          obtain ⟨w, hw⟩ := exists_ofFn_eq hlen
          exact Finset.mem_image.mpr ⟨w, Finset.mem_univ _, hw⟩
    _ = 2 ^ i := himage
  · calc 2 ^ i = (Finset.univ.image (fun w : Fin i → Bool => List.ofFn w)).card := himage.symm
      _ ≤ (distinctFactors s i).card := by
          apply Finset.card_le_card
          intro f hf
          obtain ⟨w, -, rfl⟩ := Finset.mem_image.mp hf
          exact h _ List.length_ofFn

/-- Step 1 of the de Bruijn argument: a word that contains every `k`-gram contains every
shorter `i`-gram as well — pad the `i`-gram on the right to a `k`-gram and cut the found
occurrence back down. -/
theorem coversAllWords_mono {k i : ℕ} (h : CoversAllWords s k) (hik : i ≤ k) :
    CoversAllWords s i := by
  intro w hw
  set w' : List Bool := w ++ List.replicate (k - i) false with hw'def
  have hw' : w'.length = k := by
    rw [hw'def, List.length_append, hw, List.length_replicate]
    omega
  obtain ⟨p, hpn, hp⟩ := mem_distinctFactors.mp (h w' hw')
  rw [mem_distinctFactors]
  refine ⟨p, by omega, ?_⟩
  calc (s.drop p).take i = ((s.drop p).take k).take i := by
        rw [List.take_take, min_eq_left hik]
    _ = w'.take i := by rw [hp]
    _ = w := by rw [hw'def, ← hw, List.take_left]

/-! ### The two numerical facts behind `δ(B_k) = 2^k/k` -/

/-- `d_i ≤ s.length - i + 1`: there are only that many positions a length-`i` factor can
start at. -/
theorem card_distinctFactors_le (s : List Bool) (i : ℕ) :
    (distinctFactors s i).card ≤ s.length - i + 1 := by
  calc (distinctFactors s i).card
      ≤ ((Finset.range (s.length + 1)).filter (fun p => p + i ≤ s.length)).card :=
        Finset.card_image_le
    _ ≤ (Finset.range (s.length - i + 1)).card := by
        apply Finset.card_le_card
        intro p hp
        simp only [Finset.mem_filter, Finset.mem_range] at hp ⊢
        omega
    _ = s.length - i + 1 := Finset.card_range _

/-- Cross-multiplication: `a/m ≤ b/n` follows from `a·n ≤ b·m` for positive `m, n`. -/
theorem div_le_div_of_mul_le {a b : ℚ} {m n : ℕ} (hm : (0 : ℚ) < m) (hn : (0 : ℚ) < n)
    (h : a * n ≤ b * m) : a / m ≤ b / n := by
  rw [div_le_div_iff₀ hm hn]
  exact h

/-- `2^i · k ≤ 2^k · i` for `1 ≤ i ≤ k`, the cross-multiplied form of `2^i/i ≤ 2^k/k`:
`2^i/i` is nondecreasing on `i ≥ 1`, one step being `2^{i+1}/(i+1) ≥ 2^i/i ⟺ i ≥ 1`. -/
theorem pow_mul_le_pow_mul {i k : ℕ} (hi : 1 ≤ i) :
    i ≤ k → (2 : ℚ) ^ i * k ≤ (2 : ℚ) ^ k * i := by
  induction k with
  | zero => omega
  | succ n ih =>
    intro hik
    rcases Nat.lt_or_ge i (n + 1) with hlt | hge
    · have hprev : (2 : ℚ) ^ i * n ≤ (2 : ℚ) ^ n * i := ih (by omega)
      have hle : (2 : ℚ) ^ i ≤ (2 : ℚ) ^ n := by
        apply pow_le_pow_right₀ (by norm_num : (1 : ℚ) ≤ 2)
        omega
      have hni : (2 : ℚ) ^ n ≤ (2 : ℚ) ^ n * i := by
        apply le_mul_of_one_le_right (by positivity)
        exact_mod_cast hi
      have hcast : ((n + 1 : ℕ) : ℚ) = (n : ℚ) + 1 := by push_cast; ring
      rw [hcast, pow_succ]
      nlinarith [hprev, hle, hni]
    · have hin : i = n + 1 := by omega
      rw [hin]

/-- `2^i/i ≤ 2^k/k` for `1 ≤ i ≤ k`. -/
theorem ratio_mono {i k : ℕ} (hi : 1 ≤ i) (hik : i ≤ k) :
    (2 ^ i : ℚ) / i ≤ (2 ^ k : ℚ) / k :=
  div_le_div_of_mul_le (by exact_mod_cast hi) (by exact_mod_cast (by omega : 0 < k))
    (pow_mul_le_pow_mul hi hik)

/-- Past the de Bruijn order the count of positions, `2^k + k - i`, is small enough:
`(2^k + k - i)/i ≤ 2^k/k` for `k < i ≤ 2^k + k`, because that inequality is
`(k - i) · (2^k + k) ≤ 0`. -/
theorem ratio_le_of_lt {k i : ℕ} (hk1 : 1 ≤ k) (hki : k < i) (hib : i ≤ 2 ^ k + k) :
    ((2 ^ k + k - i : ℕ) : ℚ) / i ≤ (2 ^ k : ℚ) / k := by
  have hk0 : (0 : ℚ) < k := by
    have : 0 < k := by omega
    exact_mod_cast this
  have hi0 : (0 : ℚ) < i := by
    have : 0 < i := by omega
    exact_mod_cast this
  refine div_le_div_of_mul_le hi0 hk0 ?_
  have hcast : ((2 ^ k + k - i : ℕ) : ℚ) = (2 : ℚ) ^ k + (k : ℚ) - (i : ℚ) := by
    rw [Nat.cast_sub hib]
    push_cast
    ring
  rw [hcast]
  have hnonpos : ((k : ℚ) - (i : ℚ)) * ((2 : ℚ) ^ k + (k : ℚ)) ≤ 0 := by
    apply mul_nonpos_of_nonpos_of_nonneg
    · have : (k : ℚ) ≤ (i : ℚ) := by exact_mod_cast le_of_lt hki
      linarith
    · positivity
  nlinarith [hnonpos]

/-! ### M1: `δ` of a de Bruijn word -/

/-- A finite supremum equals `c` as soon as `c` is attained and dominates every term. -/
theorem sup'_eq_of_le_of_mem {ι : Type*} {t : Finset ι} {H : t.Nonempty} {f : ι → ℚ} {a : ι}
    {c : ℚ} (ha : a ∈ t) (hfa : f a = c) (h : ∀ b ∈ t, f b ≤ c) : t.sup' H f = c :=
  le_antisymm (Finset.sup'_le H f h) (hfa ▸ Finset.le_sup' f ha)

/-- **`δ = 2^k/k`** for a de Bruijn word of order `k ≥ 2`: `d_i = 2^i` for `i ≤ k` and the
maximum of `2^i/i` is at `i = k`; for `i > k` the position count keeps `d_i/i` below it. -/
theorem deltaQ_isDeBruijn {k : ℕ} (hk : 2 ≤ k) (h : IsDeBruijn s k) :
    deltaQ s = (2 ^ k : ℚ) / k := by
  obtain ⟨hlen, hcov⟩ := h
  have hkl : 1 ≤ k := by omega
  have h2k : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  have hpos : 1 ≤ s.length := by
    rw [hlen]
    omega
  have hkmem : k ∈ Finset.Icc 1 s.length :=
    Finset.mem_Icc.mpr ⟨hkl, by rw [hlen]; omega⟩
  have hdk : ((distinctFactors s k).card : ℚ) / k = (2 ^ k : ℚ) / k := by
    rw [card_distinctFactors_of_coversAllWords hcov]
    push_cast
    ring
  unfold deltaQ
  rw [dite_eq_left hpos]
  refine sup'_eq_of_le_of_mem (f := fun i => ((distinctFactors s i).card : ℚ) / i)
    hkmem hdk ?_
  intro i hi
  obtain ⟨hi1, hile⟩ := Finset.mem_Icc.mp hi
  rcases Nat.lt_or_ge i (k + 1) with hlt | hge
  · have hik : i ≤ k := by omega
    have hci : ((distinctFactors s i).card : ℚ) = 2 ^ i := by
      rw [card_distinctFactors_of_coversAllWords (coversAllWords_mono hcov hik)]
      push_cast
      ring
    rw [hci]
    exact ratio_mono hi1 hik
  · have hki : k < i := by omega
    have hi0 : (0 : ℚ) < (i : ℚ) := by
      have : 0 < i := by omega
      exact_mod_cast this
    have hcard : ((distinctFactors s i).card : ℚ) ≤ (2 : ℚ) ^ k + (k : ℚ) - (i : ℚ) := by
      have h3 : (distinctFactors s i).card ≤ 2 ^ k + k - i := by
        have h1 := card_distinctFactors_le s i
        omega
      have h4 : ((2 ^ k + k - i : ℕ) : ℚ) = (2 : ℚ) ^ k + (k : ℚ) - (i : ℚ) := by
        rw [Nat.cast_sub (by omega : i ≤ 2 ^ k + k)]
        push_cast
        ring
      calc ((distinctFactors s i).card : ℚ) ≤ ((2 ^ k + k - i : ℕ) : ℚ) := by exact_mod_cast h3
        _ = _ := h4
    calc ((distinctFactors s i).card : ℚ) / i ≤ ((2 : ℚ) ^ k + (k : ℚ) - (i : ℚ)) / i :=
          div_le_div_of_mul_le hi0 hi0 (mul_le_mul_of_nonneg_right hcard (by positivity))
      _ = ((2 ^ k + k - i : ℕ) : ℚ) / i := by
          rw [Nat.cast_sub (by omega : i ≤ 2 ^ k + k)]
          push_cast
          ring_nf
      _ ≤ (2 ^ k : ℚ) / k := ratio_le_of_lt hkl hki (by omega)

/-! ### M2: the separation `γ ≥ 2^k/k` -/

/-- **The separation**: a binary de Bruijn word of order `k ≥ 2` has `γ ≥ 2^k/k`
(`δ ≤ γ`, KNP Lemma II.4, is `deltaQ_le_minAttractorSize`). -/
theorem gamma_ge_of_isDeBruijn {k : ℕ} (hk : 2 ≤ k) (h : IsDeBruijn s k) :
    (2 ^ k : ℚ) / k ≤ (minAttractorSize s : ℚ) := by
  rw [← deltaQ_isDeBruijn hk h]
  exact deltaQ_le_minAttractorSize s

/-! ### M3: non-vacuity — the hypothesis is inhabited at `k = 2` and `k = 3` -/

/-- `00110` is a de Bruijn word of order `2`: its `2`-grams are `00`, `01`, `11`, `10`. -/
theorem isDeBruijn_two : IsDeBruijn (['0', '0', '1', '1', '0'].map (· = '1')) 2 := by
  refine ⟨by decide, ?_⟩
  rw [coversAllWords_iff_fin]
  decide

/-- `0001011100` is a de Bruijn word of order `3`: its eight `3`-grams are the eight binary
words of length `3`. -/
theorem isDeBruijn_three :
    IsDeBruijn (['0', '0', '0', '1', '0', '1', '1', '1', '0', '0'].map (· = '1')) 3 := by
  refine ⟨by decide, ?_⟩
  rw [coversAllWords_iff_fin]
  decide

/-- `δ` at the witnesses: `2` for `00110` and `8/3` for `0001011100`.  The second is not an
integer, which is why this lane states `δ` as the rational `deltaQ` and not as the floored
`substringComplexity`. -/
example : deltaQ ((['0', '0', '1', '1', '0'].map (· = '1') : List Bool)) = 2 := by
  rw [deltaQ_isDeBruijn (by norm_num : 2 ≤ 2) isDeBruijn_two]
  norm_num

example :
    deltaQ ((['0', '0', '0', '1', '0', '1', '1', '1', '0', '0'].map (· = '1') : List Bool)) =
      8 / 3 := by
  rw [deltaQ_isDeBruijn (by norm_num : 2 ≤ 3) isDeBruijn_three]
  norm_num

/-- The separation at the witnesses: `γ(00110) ≥ 2` and `γ(0001011100) ≥ 8/3`. -/
example : (2 : ℚ) ≤ (minAttractorSize [false, false, true, true, false] : ℚ) := by
  have h := gamma_ge_of_isDeBruijn (s := [false, false, true, true, false])
    (by norm_num : 2 ≤ 2) isDeBruijn_two
  norm_num at h
  exact_mod_cast h

example : (8 : ℚ) / 3 ≤
    (minAttractorSize [false, false, false, true, false, true, true, true, false, false] : ℚ) := by
  have h := gamma_ge_of_isDeBruijn
    (s := [false, false, false, true, false, true, true, true, false, false])
    (by norm_num : 2 ≤ 3) isDeBruijn_three
  norm_num at h
  exact_mod_cast h

/-- `CoversAllWords` is not automatic: `0010` has the `2`-grams `00`, `01`, `10` but not
`11`.  So `IsDeBruijn`'s coverage hypothesis does real work. -/
example : ¬ CoversAllWords (['0', '0', '1', '0'].map (· = '1')) 2 := by
  rw [coversAllWords_iff_fin]
  decide

/-- The length condition of `IsDeBruijn` bites too: `0011` has `2`-grams `00`, `01`, `11`
(so it is a proper prefix of the order-`2` word `00110`) but length `4 ≠ 2^2 + 2 - 1`. -/
example : ¬ IsDeBruijn (['0', '0', '1', '1'].map (· = '1')) 2 := by
  intro h
  have hl : (['0', '0', '1', '1'].map (· = '1') : List Bool).length = 2 ^ 2 + 2 - 1 := h.1
  revert hl
  decide

/-! ### What this file does *not* prove

The research note (`docs/research/gamma-vs-gamma2.md`) concludes `γ(B_k)/γ₂(B_k) → ∞` from
`γ(B_k) ≥ 2^k/k` **and** `γ₂(B_k) ≤ 4`.  Only the first factor is a theorem here: `γ₂` — the
minimum size of a set covering every factor of length *at most* `2` — is not defined in this
repository, and its bound `γ₂ ≤ 4` is the elementary "one position per distinct `2`-gram".
So the quotient statement is not machine-checked; `gamma_ge_of_isDeBruijn` is the half this
lane owns. -/

end SortBounds.Projects.DeBruijn
