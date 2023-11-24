TESTS=$(sort $(basename $(wildcard test*.lama)))

LAMAI=../build/lamai

.PHONY: check $(TESTS)

check: $(TESTS)

$(TESTS): %: %.lama
	@echo $@
	cat $@.input | $(LAMAI) $@.bc > $@.log && diff $@.log orig/$@.log

clean:
	$(RM) test*.log *.s *~ $(TESTS) *.i
	$(MAKE) clean -C expressions
	$(MAKE) clean -C deep-expressions
