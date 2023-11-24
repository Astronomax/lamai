TESTS=$(sort $(basename $(wildcard generated*.lama)))

LAMAI=../../build/lamai

.PHONY: check $(TESTS)

check: $(TESTS)

$(TESTS): %: %.lama
	@echo $@
	cat $@.input | $(LAMAI) $@.bc > $@.log && diff $@.log orig/$@.log

clean:
	rm -f *.log *.s *~
	find . -maxdepth 1 -type f -not -name '*.*' -not -name 'Makefile' -delete

