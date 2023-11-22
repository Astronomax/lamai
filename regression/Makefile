TESTS=$(sort $(basename $(wildcard test*.lama)))

LAMAI=../lamai

.PHONY: check $(TESTS)

check: $(TESTS)

$(TESTS): %: %.lama
	@echo $@
	lamac -b $< > $@.bc && cat $@.input | $(LAMAI) $@.bc > $@.log && diff $@.log orig/$@.log

clean:
	$(RM) test*.log test*.bc *.s *~ $(TESTS) *.i
	$(MAKE) clean -C expressions
	$(MAKE) clean -C deep-expressions
