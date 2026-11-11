.PHONY: build axioms check clean

build:
	lake build

axioms:
	lake env lean scripts/axioms.lean

# Trust check: no declaration may use `sorry` (Lean warns "declaration uses 'sorry'"),
# and no axiom declarations or native_decide in the library sources.
check: build
	@if lake build 2>&1 | grep -q "declaration uses"; then \
		echo "FAIL: a declaration uses sorry"; exit 1; fi
	@if grep -rn --include='*.lean' -E "^[[:space:]]*(private[[:space:]]+)?axiom[[:space:]]|native_decide" SortBounds/ ; then \
		echo "FAIL: axiom declaration or native_decide in SortBounds/"; exit 1; fi
	@echo "clean: no sorry in any declaration, no axiom/native_decide in SortBounds/**/*.lean"

clean:
	lake clean
