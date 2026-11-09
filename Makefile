.PHONY: build axioms check clean

build:
	lake build

axioms:
	lake env lean scripts/axioms.lean

check: build
	@if grep -rn "\bsorry\b\|\badmit\b\|^axiom\|[^.]\baxiom\b" SortBounds/ scripts/ ; then \
		echo "FAIL: sorry/admit/axiom found"; exit 1; else echo "no sorry/admit/axiom"; fi

clean:
	lake clean
