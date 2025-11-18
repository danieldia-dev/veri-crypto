# Makefile for Veri-Crypto Verification

# Variables
PROJECT = veri-crypto
# The command is 'cargo hax', not 'hax'
HAX = cargo hax
CARGO = cargo
FSTAR = fstar.exe
LEAN = lake

# Directories
SRC_DIR = .
PROOF_DIR = proofs
FSTAR_DIR = $(PROOF_DIR)/fstar
LEAN_DIR = $(PROOF_DIR)/lean
COQ_DIR = $(PROOF_DIR)/coq

# Source files
RUST_SOURCES = lib.rs core.rs sponge.rs utils.rs hash.rs kdf.rs
VERIFIED_MODULES = core sponge utils

# Phony targets
.PHONY: all clean build test verify verify-fstar verify-lean verify-coq extract

# Default target
all: build test verify

# Build the Rust library
build:
	@echo "Building Rust library..."
	$(CARGO) build 

# Run tests
test:
	@echo "Running tests..."
	$(CARGO) test --features verification
	@echo "Running verification tests..."
	$(CARGO) test --features verification verification_tests

# Clean build artifacts
clean:
	@echo "Cleaning..."
	$(CARGO) clean
	rm -rf $(PROOF_DIR)
	rm -f *.fst *.fsti *.lean *.v

# Create proof directories
$(PROOF_DIR):
	mkdir -p $(FSTAR_DIR)
	mkdir -p $(LEAN_DIR)
	mkdir -p $(COQ_DIR)

# Extract verification conditions with hax
extract: $(PROOF_DIR)
	@echo "Extracting verification conditions..."
	# Removed --interfaces and -i lib.rs, as cargo-hax runs on the whole crate
	$(HAX) into fstar
	@echo "Moving F* files..."
	mv *.fst *.fsti $(FSTAR_DIR)/ 2>/dev/null || true
	@echo "Extracting to Lean..."
	# Removed -i lib.rs
	$(HAX) into lean
	mv *.lean $(LEAN_DIR)/ 2>/dev/null || true

# Verify with F*
verify-fstar: extract
	@echo "Verifying with F*..."
	cd $(FSTAR_DIR) && \
	$(FSTAR) --cache_checked_modules \
			--already_cached '*' \
			--fuel 8 --ifuel 2 --z3rlimit 100 \
			Core.fst Sponge.fst Utils.fst

# Verify with Lean 4
verify-lean: extract
	@echo "Verifying with Lean 4..."
	cd $(LEAN_DIR) && \
	echo 'import Lake\nopen Lake DSL\n\npackage veriRustCrypto\n\nlean_lib Core\nlean_lib Sponge\nlean_lib Utils' > lakefile.lean && \
	$(LEAN) build

# Verify with Coq (if available)
verify-coq: extract
	@echo "Extracting to Coq..."
	# Removed -i lib.rs
	$(HAX) into coq || echo "Coq backend not available"
	@if [ -f "*.v" ]; then \
		mv *.v $(COQ_DIR)/; \
		cd $(COQ_DIR) && coqc *.v; \
	fi

# Main verification target
verify: verify-fstar
	@echo "Verification complete!"

# Generate verification report
report:
	@echo "Generating verification report..."
	@echo "# Verification Report" > verification_report.md
	@echo "" >> verification_report.md
	@echo "## Module Status" >> verification_report.md
	@echo "" >> verification_report.md
	@echo "| Module | F* | Lean | Coq |" >> verification_report.md
	@echo "|--------|----|----|-----|" >> verification_report.md
	@for mod in $(VERIFIED_MODULES); do \
		echo "| $$mod | ❓ | ❓ | ❓ |" >> verification_report.md; \
	done
	@echo "" >> verification_report.md
	@echo "Generated: $$(date)" >> verification_report.md

# Install hax (if not installed)
install-hax:
	@echo "Installing hax..."
	# The package name is 'cargo-hax'
	cargo install --git https://github.com/hacspec/hax cargo-hax

# Check dependencies
check-deps:
	@echo "Checking dependencies..."
	@which $(CARGO) > /dev/null || echo "❌ Cargo not found"
	# The binary is 'cargo-hax', which provides the 'cargo hax' command
	@which cargo-hax > /dev/null || echo "❌ Hax not found (run 'make install-hax')"
	@which $(FSTAR) > /dev/null || echo "❌ F* not found"
	@which $(LEAN) > /dev/null || echo "❌ Lean 4 not found"
	@echo "✅ Dependency check complete"

# Help target
help:
	@echo "Veri-Crypto Verification Makefile"
	@echo ""
	@echo "Targets:"
	@echo "  make build         - Build the Rust library"
	@echo "  make test          - Run all tests"
	@echo "  make verify        - Run formal verification (F*)"
	@echo "  make verify-lean   - Run Lean 4 verification"
	@echo "  make verify-coq    - Run Coq verification"
	@echo "  make extract       - Extract verification conditions"
	@echo "  make report        - Generate verification report"
	@echo "  make clean         - Clean all artifacts"
	@echo "  make check-deps    - Check for required tools"
	@echo "  make install-hax   - Install hax tool"
	@echo "  make help          - Show this help"