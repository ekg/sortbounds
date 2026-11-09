.PHONY: build axioms check clean

build:
	lake build

axioms:
	lake env lean scripts/axioms.lean

check: build
	@if grep -rn "\bsorry\b\|\badmit\b\|native_decide\|^axiom\|[^.]\baxiom\b" SortBounds/ ; then \
		echo "FAIL: sorry/admit/axiom/native_decide found in SortBounds/"; exit 1; \
	else echo "clean: no sorry/admit/axiom/native_decide in SortBounds/"; fi

clean:
	lake clean
