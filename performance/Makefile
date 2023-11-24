TESTS=$(sort $(basename $(wildcard *.lama)))

LAMAI=../lamai
LAMAC=lamac

.PHONY: check $(TESTS)

check: $(TESTS)

$(TESTS): %: %.lama
	@echo "Recursive approach:"
	@echo 0 | LAMA=../runtime `which time` -f "$@\t%U" $(LAMAC) -s $< > $@.log
	@echo "Iterative approach:"
	@echo 0 | `which time` -f "$@\t%U" sh -c 'lamac -b $< > $@.bc && $(LAMAI) $@.bc'

clean:
	$(RM) test*.log *.bc *.s *~ $(TESTS) *.i
