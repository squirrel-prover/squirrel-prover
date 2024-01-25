PREFIX = ~/.local
SQUIRRELBIN = $(PREFIX)/bin

ECHO = /usr/bin/env echo

default: squirrel ## By default, just build Squirrel.

.PHONY: test
test: alcotest_full example ## Run alcotests (see ./test.ml) and examples.

all: squirrel test ## Build Squirrel and run tests.

.PHONY: doc
doc: ## Generate user manual and API documentation.
	dune build @refman-html
	dune build @doc
	@$(ECHO) "API doc available: _build/default/_doc/_html/squirrel/index.html"
	@$(ECHO) "User manual available: _build/default/documentation/sphinx/public/index.html"

.PHONY: start
start: jsquirrel bundle ## Start JSquirrel on a local HTTP server.
	dune exec $(APPDIR)server/server.exe

.PHONY: help
help: ## Print this help message.
	@echo "List of available make commands:";
	@echo "";
	@grep -E '^[a-zA-Z_-]+:.*?## .*$$' $(MAKEFILE_LIST) | awk 'BEGIN {FS = ":.*?## "}; {printf "  \033[36m%-15s\033[0m %s\n", $$1, $$2}';
	@echo "";

# squirrel is not PHONY here, it exists as executable
.PHONY: okfail okfail_end example examples_end alcotest alcotest_full

# -----------------------------------------------------------------------
# Tests
# -----------------------------------------------------------------------

# Directory for logging test runs on "*.sp" files.
RUNLOGDIR=_build/squirrel_log
BENCHDIR=_build/bench
TESTS_OUT=_build/default/tests.output

NOW=`date +"%m_%d_%Y_%H_%M"`
BENCH_OUT=$(BENCHDIR)/last.json
BENCH_COMMIT_OUT=$(BENCHDIR)/$(GITCOMMIT).json

ORA=\033[0;33m
RED=\033[0;31m
GRE=\033[0;32m
NC=\033[0m

# Make sure the "echo" commands in okfail below are updated
# to reflect the content of these variables.
PROVER_TESTS = $(wildcard tests/ok/*.sp) $(wildcard tests/fail/*.sp)

PROVER_EXAMPLES =\
  $(wildcard examples/*.sp)                     \
  $(wildcard examples/tutorial/*.sp)            \
  $(wildcard examples/tutorial/solutions/*.sp)  \
  $(wildcard examples/basic-tutorial/*.sp)      \
  $(wildcard examples/stateful/*.sp)            \
  $(wildcard examples/postQuantumKE/*.sp)       \
  $(wildcard examples/ho/authdh.sp)             \
  $(wildcard examples/ho/hybrid.sp)             \
  $(wildcard examples/crypto/*.sp)

BENCH_JSON = $(wildcard $(BENCHDIR)/prev/*.json)

okfail: squirrel
	rm -rf $(RUNLOGDIR)
	@$(ECHO) "Running tests/ok/*.sp and tests/fail/*.sp."
	@$(MAKE) -j8 okfail_end

# Run PROVER_TESTS as a dependency, then check for errors.
okfail_end: $(PROVER_TESTS:.sp=.ok)
	@$(ECHO)
	@if test -f tests/tests.ko ; then \
	  wc -l < tests/tests.ko | tr -d '\n'; $(ECHO) " tests failed:" ; \
	  cat tests/tests.ko | sort ; \
    rm -f tests/tests.ko ; exit 1 ; \
	 else $(ECHO) All tests passed successfully. ; fi

bench_preamble:
	@echo "${GRE}BENCH: ↓ For more stability in timing you can underclock your CPU ↓ ${NC}"
	@echo "${GRE}BENCH: it is recommanded to set /sys/devices/system/cpu/intel_pstate/no_turbo to 1${NC}"
	@mkdir -p $(BENCHDIR)/prev
	@echo "$(NOW): current commit → ${GRE}$(HEAD)${NC}"

# Populates $(RUNLOGDIR)/$${example%.*}.json with count tactics
tac_count_examples: squirrel
	@$(ECHO) "Counting tactics in examples/*.sp, examples/tutorial/*.sp, examples/basic-tutorial/*.sp, examples/stateful/*.sp, examples/postQuantumKE/*.sp and examples/crypto/*.sp ."
	@for example in $(PROVER_EXAMPLES); do \
		stat_name=$(RUNLOGDIR)/$${example%.*}.json;\
		mkdir -p `dirname $${stat_name}`;\
		if ./squirrel $${example} --stat $${stat_name} >/dev/null 2>/dev/null; then \
			echo "${GRE}$${stat_name} OK${NC}";\
		else \
			echo "${RED}$${stat_name} FAIL${NC}";\
		fi; \
	done
	@echo

# The following rule populate the $(BENCH_OUT) file
# in $(BENCHDIR) running /usr/bin/time on each example.
# README → /usr/bin/time is not always installed by default in your OS !
# In the same time populates $(RUNLOGDIR)/$${example%.*}.json with count tactics
$(BENCH_OUT): squirrel
	@$(ECHO) "Running bench on examples/*.sp, examples/tutorial/*.sp, examples/basic-tutorial/*.sp, examples/stateful/*.sp, examples/postQuantumKE/*.sp and examples/crypto/*.sp."
	@echo "Populate bench in $@"
	@printf "{" > $@
	@for example in $(PROVER_EXAMPLES); do \
		stat_name=$(RUNLOGDIR)/$${example%.*}.json;\
		mkdir -p `dirname $${stat_name}`;\
		printf "\"%s\" : " $${example} >> $@ ; \
		if /usr/bin/time -q -a -o $@ -f "%U" ./squirrel $${example} --stat $${stat_name} >/dev/null 2>/dev/null; then \
			$(ECHO) -n .; \
		else \
			$(ECHO) -n !; \
		fi; \
		if [ $$example != $(lastword $(PROVER_EXAMPLES)) ]; then \
			printf "," >> $@; \
		fi \
	done
	@printf "}" >> $@
	@echo

# This rule run examples and record execution time into 
# $(BENCHDIR)/prev/$(NOW).json and create a new $(BENCHDIR)/all/last.json
# A save of this bench is made in $(BENCHDIR)/all/$(NOW).json
bench_example: bench_preamble $(BENCH_OUT)
	@echo "Verify $(BENCH_OUT) and copy in $(BENCHDIR)/$(NOW).json…"
	@if python3 -m json.tool $(BENCH_OUT) > $(BENCHDIR)/prev/$(NOW).json \
		; then \
		echo "Done" ; \
	 else \
	 	rm -f $(BENCHDIR)/prev/$(NOW).json; \
		echo "${RED}[FAIL] Json malformed see $(BENCH_OUT)${NC}"; \
		echo "${RED}[FAIL] make clean_bench to remove $(BENCH_OUT)${NC}"; \
		false ;\
	fi

# The following rule combine .json files from
# $(BENCH_JSON) into $(BENCHDIR)/all/last.json
# This directory aims to be an history of previous benchmarks
$(BENCHDIR)/all/last.json:
	@mkdir -p $(BENCHDIR)/all
	@echo "Combining json files"
	@printf "{" > $@
	@for stat in $(BENCH_JSON); do \
		filename=$$(basename $${stat} .json); \
		printf "\"%s\" : " $$filename >> $@; \
		echo "$$filename OK"; \
		cat $${stat} >> $@; \
		if [ $$stat != $(lastword $(BENCH_JSON)) ]; then \
			printf "," >> $@; \
		fi \
	done 
	@printf "}" >> $@
	@echo

example: squirrel
	@rm -rf `$(RUNLOGDIR)/examples`
	@$(ECHO) "================== EXAMPLES ======================"
	@$(ECHO) "Running examples/*.sp, examples/tutorial/*.sp, examples/basic-tutorial/*.sp, examples/stateful/*.sp,  examples/postQuantumKE/*.sp and examples/crypto/*.sp."
	@$(MAKE) -j4 examples_end

# Run PROVER_EXAMPLES as a dependency, then check for errors.
examples_end: $(PROVER_EXAMPLES:.sp=.ok)
	@$(ECHO)
	@if test -f tests/tests.ko ; then \
	  wc -l < tests/tests.ko | tr -d '\n'; $(ECHO) " tests failed:" ; \
	  cat tests/tests.ko | sort ; rm -f tests/tests.ko ; exit 1 ; \
	 else $(ECHO) All examples passed successfully. ; fi

%.ok: %.sp
	@mkdir -p `dirname $(RUNLOGDIR)/$(@:.ok=.sp)`
	@if ./squirrel $(@:.ok=.sp) \
	  > $(RUNLOGDIR)/$(@:.ok=.sp) \
	  2> $(RUNLOGDIR)/$(@:.ok=.sp.stderr) \
	 ; then $(ECHO) -n . ; \
	 else $(ECHO) "[FAIL] $(@:.ok=.sp)" >> tests/tests.ko ; $(ECHO) -n '!' ; fi

# Rebuild and run tests.
# Only executes tests if dependencies have changed (?)
# relying on dune file to know (possibly runtime) dependencies.
alcotest: version
	dune runtest

# Same as above but will print out only the FAILs tests as before
alcotest_full: version 
	@$(ECHO) "================== ALCOTEST ======================"
	@dune build @mytest
	@python3 ./scripts/sed.py $(TESTS_OUT) /tmp/tests.output
	@if cat /tmp/tests.output | grep -q "^[^│] \[FAIL\]" ; \
		then echo "${RED}Alcotests FAILED :${NC}" ; \
		  cat /tmp/tests.output | grep -E --color "^[^│] \[FAIL\]" ; \
			exit 1; \
		else echo "${GRE}Alcotests passed successfully !${NC}" ; \
	fi

# -----------------------------------------------------------------------
# Cleaning
# -----------------------------------------------------------------------

.PHONY: clean
clean: ## Call dune clean and remove executable and coverage data.
	dune clean
	@rm -f squirrel
	rm -rf _coverage

# Clean last bench
.PHONY: clean_bench
clean_bench: ## Clean previous benchmark data.
	rm -f $(BENCHDIR)/*.json

# Clean previous local bench
clean_prev_bench:
	rm -f $(BENCHDIR)/prev/*.json

# Clean all local bench
.PHONY: clean_all_bench
clean_all_bench: ## Clean all benchmark data.
	rm -rf $(BENCHDIR)

# We have to "touch" ./squirrel executable for other recipes
squirrel: version
	dune build squirrel.exe
	@cp -f _build/default/squirrel.exe squirrel

# -----------------------------------------------------------------------
# Misc
# -----------------------------------------------------------------------

# Run tests (forcing a re-run) with bisect_ppx instrumentation on
# to get coverage files, and generate an HTML report from them.
# TODO also generate coverage report when running squirrel on *.sp files,
# with two options:
# 1. The instrumentation option could be passed to dune exec squirrel,
#    but the latter does not work (theories are not installed).
# 2. These tests could be ran as dune tests rather than through this
#    Makefile, which would render instrumentation available and would
#    also avoid re-runnning tests when unnecessary.
.PHONY: coverage
coverage: ## Generates coverage report in _coverage/index.html.
	rm -rf _coverage
	dune runtest --force --instrument-with bisect_ppx
	find . -name '*.coverage' | \
	  xargs bisect-ppx-report html --ignore-missing-files
	find . -name '*.coverage' | xargs rm -f
	@$(ECHO) "Coverage report available: _coverage/index.html"

# The install target should probably be changed to using dune,
# so that dune exec could work.
install: squirrel
	cp -f squirrel $(SQUIRRELBIN)
	cp -r theories $(SQUIRRELBIN)
	export SQUIRRELBIN=$(SQUIRRELBIN)

.PHONY: refman-html
refman-html:
	dune build --no-buffer @refman-html
	@$(ECHO) "Documentation available: _build/default/documentation/sphinx/public/index.html"

deploy-html: refman-html
	mkdir public
	cp -r _build/default/documentation/sphinx/public .

# -----------------------------------------------------------------------
# Handling of src/commit.ml
# -----------------------------------------------------------------------

.PHONY: version
version:
	@echo Regenerating src/commit.ml...
	@cat src/commit.ml.in \
	  | sed 's/GITHASH/$(shell scripts/git-hash)/' \
	  > src/commit.ml

# -----------------------------------------------------------------------
# Benchmarking examples over revisions
# -----------------------------------------------------------------------

HEAD:=$(shell git rev-parse --short HEAD)
GITCOMMIT:=$(shell git rev-parse --short HEAD~1)
LAST=`/usr/bin/ls -1t $(BENCHDIR)/prev/*.json | head -1`
LAST2=`/usr/bin/ls -1t $(BENCHDIR)/prev/*.json | head -2 | tail -1`
LAST_COMMIT=`/usr/bin/ls -1t $(BENCHDIR)/commits/*.json | head -1`
PLOT=./scripts/plot.py
STASH_RAND:= $(shell bash -c 'echo $$RANDOM')

.PHONY: bench
bench: bench_example ## Perform benchmarks (cf. wikis/Dev-README on gitlab).

# This plot tactics statistics
.PHONY: plot
plot: ## Plot data from last benchmark.
	python3 $(PLOT)

# This shows you the last benchmark compared to the mean of all previous ones
# Needs `matplotlib` (pip install)
.PHONY: plot_all
plot_all: ## Compare all benchmarks with last one.
	rm -f $(BENCHDIR)/all/last.json
	$(MAKE) $(BENCHDIR)/all/last.json
	python3 $(PLOT) $(BENCHDIR)/all/last.json

# This shows you the last benchmark compared to previous one
# Needs `matplotlib` (pip install)
.PHONY: plot_diff_last
plot_diff_last: ## Compare between last two benchmarks.
	@echo "Compare ${ORA}$(LAST2)${NC} with ${GRE}$(LAST)${NC}"
	python3 $(PLOT) $(LAST2) $(LAST) 

# This shows you the last benchmark compared to the most recent commit bench
# Needs `matplotlib` (pip install)
.PHONY: plot_diff_commit
plot_diff_commit: ## Compare last benchmark with most recent commit benchmark.
	@echo "Compare ${ORA}$(LAST_COMMIT)${NC} with ${GRE}$(LAST)${NC}"
	python3 $(PLOT) $(LAST_COMMIT) $(LAST)

# compare bench of current work with a specified commit in GITCOMMIT
# GITCOMMIT is by default to HEAD~1
.PHONY: bench_compare
bench_compare: bench_preamble $(BENCH_OUT) ## Compare benchmark with given commit (cf. Dev-README).
	@echo "↑ Bench ${GRE}master with current work${NC} ↑"
	@echo "Verify $(BENCH_OUT) and copy in $(BENCHDIR)/prev/$(NOW).json…"
	@if python3 -m json.tool $(BENCH_OUT) > $(BENCHDIR)/prev/$(NOW).json \
		; then \
		echo "Done" ; \
	 else \
	 	rm -f $(BENCHDIR)/prev/$(NOW).json; \
		echo "${RED}[FAIL] Json malformed see $(BENCH_OUT)${NC}"; \
		echo "${RED}[FAIL] make clean_bench to remove $(BENCH_OUT)${NC}"; \
		false; \
	fi
	@$(MAKE) $(BENCHDIR)/commits/$(GITCOMMIT).json
	$(MAKE) plot_diff_commit

# Populate commits/$(GITCOMMIT).json by checking out $(GITCOMMIT)
# And running the bench on its version
# The current work is stashed away before and stashed back after
# IF INTERRUPTED DON'T PANIC xP
# YOU HAVE TO STASH YOUR WORK BACK WITH git stash apply
$(BENCHDIR)/commits/%.json:
	@if git cat-file -e $(GITCOMMIT)^{commit}; then \
		echo "Compare with ${ORA}$(GITCOMMIT)${NC}"; \
	else \
		echo "${ORA}$(GITCOMMIT)${NC} does not exist"; \
		exit 0; \
	fi
	@mkdir -p $(BENCHDIR)/commits
	@echo "${RED}/!\ DO NOT INTERRUPT /!\ ${NC}"
	@echo "${RED}If something goes wrong: ${NC}"
	@echo "${RED}- If you are in version $(GITCOMMIT): git switch - ${NC}"
	@echo "${RED}- If you want your current work back: git stash pop ${NC}"
	@echo "${ORA}Stashing current work as $(STASH_RAND)${NC}"
	git stash -m "$(STASH_RAND)"
	@echo "Checkout ${ORA}$(GITCOMMIT)${NC}"
	git checkout $(GITCOMMIT) --quiet  
	@echo "Building ${ORA}$(GITCOMMIT)"
	# Call the actual commit make
	@make
	@echo "Populate bench in $(BENCH_COMMIT_OUT)"
	@printf "{" > $(BENCH_COMMIT_OUT)
	@for ex in $(PROVER_EXAMPLES); do \
		printf "\"%s\" : " $${ex} >> $(BENCH_COMMIT_OUT) ; \
		if /usr/bin/time -q -a -o $(BENCH_COMMIT_OUT) -f "%U" ./squirrel $${ex} >/dev/null 2>/dev/null; then \
			$(ECHO) -n .; \
		else \
			$(ECHO) -n !; \
		fi; \
		if [ $$ex != $(lastword $(PROVER_EXAMPLES)) ]; then \
		printf "," >> $(BENCH_COMMIT_OUT); \
		else \
		printf "}" >> $(BENCH_COMMIT_OUT); \
		fi \
	done
	@echo
	@echo "Verify $(BENCH_COMMIT_OUT) and copy in $(BENCHDIR)/commits/$(GITCOMMIT).json…"
	@if python3 -m json.tool $(BENCH_COMMIT_OUT) > $(BENCHDIR)/commits/$(GITCOMMIT).json \
		; then \
		echo "Done" ; \
		rm -f $(BENCH_COMMIT_OUT) ; \
	 else \
	 	rm -f $(BENCHDIR)/commits/$(GITCOMMIT).json; \
		echo "${RED}[FAIL] Json malformed: see $(BENCH_COMMIT_OUT)${NC}"; \
		echo "${RED}[FAIL] The script wil ignore it and continue… ${NC}"; \
	fi
	@echo "${NC}Back to master…"
	git switch -
	@echo "${GRE}Stashing $(STASH_RAND) back current work if it exists${NC}"
	@if git stash list | grep "$(STASH_RAND)" && git stash pop --index --quiet \
		; then \
		echo "Done" ; \
	else \
		echo "No work pop back from stash"; \
	fi

# -----------------------------------------------------------------------
# JSquirrel
# -----------------------------------------------------------------------

APPDIR=app/

# TODO in dune !
jsquirrel: 
	rm -f app/www/static/client.bc.js
	dune build app/www/static/client.bc.js
	mkdir -p app/www/static/theories
	cp ./theories/*.sp app/www/static/theories/.
	cp ./examples/tutorial/*.sp app/www/static/theories/.

bundle:
	mkdir -p $(APPDIR)www/static
	# rm -f app/www/static/editor.bundle.js
	# dune build app/www/static/editor.bundle.js
	npm run prepare --prefix app/

zipsquirrel: jsquirrel bundle refman-html
	rm -rf _build/default/zipdir
	mkdir _build/default/zipdir
	cp -r _build/default/documentation/sphinx/public _build/default/zipdir/documentation
	cp -r _build/default/app/www/* _build/default/zipdir/.
	cd _build/default/zipdir && \
	zip -r jsquirrel.zip *
