# One target per flavour: sorry/admit/native_decide check, then build. There is deliberately
# no target that checks all of them -- the flavours share nothing, so a sweep only proves that
# four things you did not touch still compile.

FLAVOURS := StsMultisetLog StsStepInductive StsReactionInLabel StsConditionSplit StsRelationalSetLog

# Textual, so it also covers files a build would not reach. Backtick-quoted mentions in
# docstrings are exempt. `native_decide` is banned too: it would let a `decide`-style claim be
# discharged by compiled code outside the kernel.
BANNED_RE := (^|[^`[:alnum:]_])(sorry|admit|native_decide)([^`[:alnum:]_]|$$)

.DEFAULT_GOAL := help
.PHONY: help cache $(FLAVOURS) $(addsuffix -sorry,$(FLAVOURS)) $(addsuffix -build,$(FLAVOURS)) \
        majorum majorum-sorry majorum-build

help:
	@echo 'make cache       - fetch prebuilt Mathlib artifacts'
	@echo 'make <flavour>   - sorry/admit check + build of one flavour'
	@echo '                   flavours: $(FLAVOURS)'
	@echo 'make <flavour>-sorry / -build  - either half on its own'
	@echo 'make majorum     - same, for the worked example under Examples/'
	@echo
	@echo 'What each flavour is, and its status: see README.md.'

cache:
	lake exe cache get

define FLAVOUR_RULES
$(1): $(1)-sorry $(1)-build

$(1)-sorry:
	@if grep -rnE '$$(BANNED_RE)' --include='*.lean' $(1) $(1).lean; then \
		echo 'FAIL: sorry/admit/native_decide found in $(1)'; exit 1; \
	else \
		echo 'sorry/admit check passed ($(1))'; \
	fi

$(1)-build:
	lake build $(1)
endef

$(foreach f,$(FLAVOURS),$(eval $(call FLAVOUR_RULES,$(f))))

# A worked example is not a flavour: it lives at Examples/<flavour>/<protocol>, and its lib name
# is not its directory, so it gets its own rule rather than joining FLAVOURS.
MAJORUM_DIR := Examples/StsMultisetLog/majorum

majorum: majorum-sorry majorum-build

majorum-sorry:
	@if grep -rnE '$(BANNED_RE)' --include='*.lean' $(MAJORUM_DIR) $(MAJORUM_DIR).lean; then \
		echo 'FAIL: sorry/admit/native_decide found in majorum'; exit 1; \
	else \
		echo 'sorry/admit check passed (majorum)'; \
	fi

majorum-build:
	lake build MajorumExample
