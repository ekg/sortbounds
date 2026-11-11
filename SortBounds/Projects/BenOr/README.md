# Lane: BenOr — algebraic decision trees

**Question.** In the comparison model each test has 2 outcomes, so `b = 2` and
the bound is `log₂(n!)`. In an *algebraic* decision tree a test asks for the sign
of a polynomial, so `b = 3` and the bound `log₂(n!)` weakens — yet Ben-Or (1983)
recovers `Ω(n log n)` for element distinctness from **topology**: the number of
connected components of the set being decided. This is the standard example of
"the model changes, and the answer changes for non-obvious reasons".

**Why it matters.** It is the honest boundary of our result: our theorem is about
bits per *binary* probe. Ben-Or's is about bits per *component*, and no one has
machine-checked it.

## Contract (M0 only is committed)

```lean
namespace SortBounds.Projects.BenOr

/-- An algebraic decision tree over `n` real variables: branch on the sign of a
polynomial, leaves accept/reject. -/
inductive ADT (n : ℕ) where
  | leaf : Bool → ADT n
  | node : MvPolynomial (Fin n) ℚ → ADT n → ADT n → ADT n

def ADT.height : ADT n → ℕ
/-- `t` decides `S` if every input reaches a leaf whose label matches `S`. -/
def ADT.decides (t : ADT n) (S : Set (Fin n → ℚ)) : Prop

/-- The combinatorial shadow of Ben-Or: height `h` ⇒ at most `2^h` cells. -/
theorem ADT.card_cells_le (t : ADT n) : t.numCells ≤ 2 ^ t.height

/-- The *statement* of Ben-Or's bound, as a documented `Prop` (M2 target;
do not prove by `sorry`). -/
def BenOrBound : Prop

end SortBounds.Projects.BenOr
```

## Milestones

* **M0** the `ADT` datatype, `height`, `decides`, and the leaf-counting corollary
  (`b = 2`, reuse `Core.Branching`'s idea). Everything must compile.
* **M1** *gated*: `BenOrBound` specialised to element distinctness, i.e. the
  statement that `{x | all xᵢ distinct}` has `n!` connected components. Real
  algebraic geometry; state it, cite Ben-Or 1983, do not attempt a proof.
* **M2** *gated*: the bound itself. Not committed.

**Deliverable = a precise, compiled statement of the theorem plus its model.**
That alone is useful: it makes "the model changes the answer" machine-readable.

## Rules

Own only `SortBounds/Projects/BenOr/`. `lake env lean`. No `sorry`. A `def
BenOrBound : Prop := …` with no proof is the correct shape for the unproved part.

## Prior art

Ben-Or 1983 (STOC, topological method); Milnor–Thom component bounds. No
formalization found.

## Log

* (empty)
