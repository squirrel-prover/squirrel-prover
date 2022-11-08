GITHASH := $(shell scripts/git-hash)

PREFIX = ~/.local

ECHO = /bin/echo

default: squirrel

all: squirrel test

test: alcotest okfail example

bench: bench_example 

.PHONY: okfail okfail_end example examples_end alcotest squirrel

# Directory for logging test runs on "*.sp" files.
RUNLOGDIR=_build/squirrel_log
BENCHDIR=_build/squirrel_log/bench

NOW=`date +"%m_%d_%Y_%H_%M"`

# Make sure the "echo" commands in okfail below are updated
# to reflect the content of these variables.
PROVER_TESTS = $(wildcard tests/ok/*.sp) $(wildcard tests/fail/*.sp)
PROVER_EXAMPLES = $(wildcard examples/*.sp) $(wildcard examples/tutorial/*.sp) $(wildcard examples/tutorial/solutions/*.sp) $(wildcard examples/stateful/*.sp)  $(wildcard examples/postQuantumKE/*.sp)
BENCH_JSON = $(wildcard $(BENCHDIR)/prev/*.json)

okfail: squirrel
	rm -rf $(RUNLOGDIR)
	@$(ECHO) "Running tests/ok/*.sp and tests/fail/*.sp."
	@$(MAKE) -j8 okfail_end

# Run PROVER_TESTS as a dependency, then check for errors.
okfail_end: $(PROVER_TESTS:.sp=.ok)
	@$(ECHO)
	@if test -f tests/tests.ko ; then \
	  wc -l tests/tests.ko | cut -f 1 -d " "; $(ECHO) " tests failed:" ; \
	  cat tests/tests.ko | sort ; \
    rm -f tests/tests.ko ; exit 1 ; \
	 else $(ECHO) All tests passed successfully. ; fi

# This rule run examples and record execution time into 
# $(BENCHDIR)/prev/$(NOW).json and create a new $(BENCHDIR)/all/last.json
# A save of this bench is made in $(BENCHDIR)/all/$(NOW).json
bench_example:
	@mkdir -p $(BENCHDIR)/prev
	@mkdir -p $(BENCHDIR)/all
	@$(ECHO) "$(NOW)"
	@$(ECHO) "Running bench on examples/*.sp, examples/tutorial/*.sp, examples/stateful/*.sp and examples/postQuantumKE/*.sp."
	@$(MAKE) -j1 $(BENCHDIR)/tmp.json
	@echo "Verify tmp.json in $(BENCHDIR)/$(NOW).json…"
	@if python -m json.tool $(BENCHDIR)/tmp.json > $(BENCHDIR)/prev/$(NOW).json \
	 ; then $(ECHO) "Done" ; \
	 else $(ECHO) "[FAIL] Json malformed"; fi
	rm -f $(BENCHDIR)/tmp.json
	@$(MAKE) $(BENCHDIR)/all/last.json
	@echo "Verify last.json in $(BENCHDIR)/all/$(NOW).json…"
	@if python -m json.tool $(BENCHDIR)/all/last.json > $(BENCHDIR)/all/$(NOW).json\
	 ; then $(ECHO) "Done" ; \
	 else $(ECHO) "[FAIL] Json malformed"; fi

# This shows you the last benchmark compared to previous one
# Needs `matplotlib` (pip install)
plot: $(BENCHDIR)/all/last.json
	python3 ./plot.py $(BENCHDIR)/all/last.json

# The following rule populate the tmp.json file
# in $(BENCHDIR) running /usr/bin/time on each example.
# README → /usr/bin/time is not always installed by default in your OS !
$(BENCHDIR)/tmp.json: $(PROVER_EXAMPLES)
	@echo "Populate bench in $@"
	@printf "{" > $@
	@for ex in $(PROVER_EXAMPLES); do \
		printf "\"%s\" : " $${ex} >> $@ ; \
		/usr/bin/time -a -o $@ -f "%U" ./squirrel $${ex} >/dev/null 2>/dev/null ; \
		if [ $$ex != $(lastword $(PROVER_EXAMPLES)) ]; then \
		printf "," >> $@; \
		else \
		printf "}" >> $@; \
		fi \
	done

# The following rule combine .json files from
# $(BENCH_JSON) into $(BENCHDIR)/all/last.json
# This directory aims to be an history of previous benchmarks
$(BENCHDIR)/all/last.json: $(BENCH_JSON)
	@echo "Combining json files"
	@printf "{" > $@
	@for stat in $(BENCH_JSON); do \
		filename=$$(basename $${stat} .json); \
		echo $$filename; \
		printf "\"%s\" : " $$filename >> $@; \
		cat $${stat} >> $@; \
		if [ $$stat != $(lastword $(BENCH_JSON)) ]; then \
		printf "," >> $@; \
		else \
		printf "}" >> $@; \
		fi; \
	done 

example: squirrel
	rm -rf `$(RUNLOGDIR)/examples`
	@$(ECHO) "Running examples/*.sp, examples/tutorial/*.sp, examples/stateful/*.sp and examples/postQuantumKE/*.sp."
	@$(MAKE) -j4 examples_end

# Run PROVER_EXAMPLES as a dependency, then check for errors.
examples_end: $(PROVER_EXAMPLES:.sp=.ok)
	@$(ECHO)
	@if test -f tests/tests.ko ; then \
	  wc -l tests/tests.ko | cut -f 1 -d " "; $(ECHO) " tests failed:" ; \
	  cat tests/tests.ko | sort ; rm -f tests/tests.ko ; exit 1 ; \
	 else $(ECHO) All tests passed successfully. ; fi

%.ok: %.sp
	@mkdir -p `dirname $(RUNLOGDIR)/$(@:.ok=.sp)`
	@if ./squirrel $(@:.ok=.sp) \
	  > $(RUNLOGDIR)/$(@:.ok=.sp) \
	  2> $(RUNLOGDIR)/$(@:.ok=.sp.stderr) \
	 ; then $(ECHO) -n . ; \
	 else $(ECHO) "[FAIL] $(@:.ok=.sp)" >> tests/tests.ko ; $(ECHO) -n '!' ; fi

# Only executes tests if dependencies have changed,
# relying on dune file to know (possibly runtime) dependencies.
alcotest: version
	dune runtest

clean:
	dune clean
	@rm -f squirrel
	rm -rf _coverage

# Clean previous bench to compare with
clean_bench:
	rm -f $(BENCHDIR)/*.json

squirrel: version
	dune build squirrel.exe
	cp -f _build/default/squirrel.exe squirrel

# Run tests (forcing a re-run) with bisect_ppx instrumentation on
# to get coverage files, and generate an HTML report from them.
# TODO also generate coverage report when running squirrel on *.sp files,
# with two options:
# 1. The instrumentation option could be passed to dune exec squirrel,
#    but the latter does not work (theories are not installed).
# 2. These tests could be ran as dune tests rather than through this
#    Makefile, which would render instrumentation available and would
#    also avoid re-runnning tests when unnecessary.
coverage:
	rm -rf _coverage
	dune runtest --force --instrument-with bisect_ppx
	find . -name '*.coverage' | \
	  xargs bisect-ppx-report html --ignore-missing-files
	find . -name '*.coverage' | xargs rm -f
	@$(ECHO) "Coverage report available: _coverage/index.html"

# The install target should probably be changed to using dune,
# so that dune exec could work.
install: squirrel
	cp -f squirrel $(PREFIX)/bin/squirrel
	cp -r theories $(PREFIX)/bin/theories

doc:
	dune build @doc
	@$(ECHO) "Documentation available: _build/default/_doc/_html/squirrel/index.html"

version:
	rm -f src/commit.ml
	sed 's/GITHASH/$(GITHASH)/' < src/commit.ml.in > src/commit.ml

.PHONY: version clean
