.PHONY: build axioms check trust clean

build:
	lake build

axioms:
	lake env lean scripts/axioms.lean

# No declaration may use `sorry` (Lean emits "declaration uses 'sorry'"), and the
# axiom audit must pass: scripts/trust.sh fails if the audit itself stops
# elaborating, if any listed theorem depends on sorryAx/native_decide, or if the
# sources contain an axiom declaration or native_decide.
check: build
	@if lake build 2>&1 | grep -q "declaration uses"; then \
		echo "FAIL: a declaration uses sorry"; exit 1; fi
	@./scripts/trust.sh

trust:
	@./scripts/trust.sh --verbose

clean:
	lake clean
