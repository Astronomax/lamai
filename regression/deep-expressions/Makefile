TESTS=$(sort $(basename $(wildcard generated*.lama)))

LAMAI=../../lamai
LAMAC=lamac

.PHONY: check $(TESTS)

check: $(TESTS)

$(TESTS): %: %.lama
	@echo $@
	$(LAMAC) -b $< > $@.bc && cat $@.input | $(LAMAI) $@.bc > $@.log && diff $@.log orig/$@.log

clean:
	rm -f *.log *.bc *.s *~
	find . -maxdepth 1 -type f -not -name '*.*' -not -name 'Makefile' -delete

