all: paper bench

paper:
	latexmk -pdf RecognitionHamiltonian_2025.tex

bench:
	python3 RecognitionScience/foundation/recognition_hamiltonian.py --coupling 0.005 --primes 200

bench-diagonal:
	python3 RecognitionScience/foundation/gln_block.py -n 10000

bench-hybrid:
	python3 RecognitionScience/foundation/hybrid_operator.py -n 20000 | tee benchmark.out

bench-validation:
	python3 RecognitionScience/foundation/validate_claims.py

quicktest:
	@echo "Quick regression test: ζ(2) and ζ(3) with 5000 primes..."
	@python3 RecognitionScience/foundation/gln_block.py -n 5000 --rank 1 | \
	  awk '/rel_err/ { err = $$NF + 0; if (err > 1e-4) { print "FAIL: " $$0 " (error " err " > 1e-4)"; exit 1 } else print "PASS: " $$0 " (error " err " <= 1e-4)" }'
	@echo "All tests passed!"

clean:
	rm -f *.aux *.log *.out *.toc *.bbl *.blg *.fls *.fdb_latexmk
	rm -f RecognitionHamiltonian_2025.pdf PrimeFredholm_2025.pdf benchmark.out

.PHONY: all paper bench bench-diagonal bench-hybrid bench-validation quicktest clean 