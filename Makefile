.PHONY: build axioms check trust clean

build:
	lake build

axioms:
	lake env lean scripts/axioms.lean

# Trust check, in three layers:
#  1. no declaration may use `sorry` (Lean emits "declaration uses 'sorry'");
#  2. no `axiom` declaration and no `native_decide` in the library sources;
#  3. every theorem listed in scripts/axioms.lean depends only on Lean's three
#     standard axioms -- no `sorryAx`, no `Lean.ofReduceBool`.
check: build
	@if lake build 2>&1 | grep -q "declaration uses"; then \
		echo "FAIL: a declaration uses sorry"; exit 1; fi
	@if grep -rn --include='*.lean' -E "^[[:space:]]*(private[[:space:]]+)?axiom[[:space:]]|native_decide" SortBounds/ ; then \
		echo "FAIL: axiom declaration or native_decide in SortBounds/"; exit 1; fi
	@if $(MAKE) -s axioms 2>&1 | grep -E "sorryAx|Lean\.ofReduceBool"; then \
		echo "FAIL: a listed theorem depends on sorryAx or native_decide"; exit 1; fi
	@echo "clean: no sorry, no axiom/native_decide, and every listed theorem is axiom-standard"

# Just the axiom audit, non-silent.
trust: axioms
	@$(MAKE) -s axioms 2>&1 | grep -c "depends on axioms" | xargs -I{} echo "{} theorems axiom-checked"

clean:
	lake clean
