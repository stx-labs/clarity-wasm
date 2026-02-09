# Contributing to clar2wasm

Thank you for your interest in contributing to clar2wasm! This document provides guidelines and information for contributors.

## Table of Contents

- [Getting Started](#getting-started)
- [Development Environment](#development-environment)
- [Code Style](#code-style)
- [Testing](#testing)
- [Pull Request Process](#pull-request-process)
- [Code of Conduct](#code-of-conduct)

## Getting Started

1. **Fork the repository** on GitHub
2. **Clone your fork** with submodules:
   ```sh
   git clone --recurse-submodules https://github.com/YOUR_USERNAME/clarity-wasm.git
   ```
3. **Create a branch** for your changes:
   ```sh
   git checkout -b feature/your-feature-name
   ```

## Development Environment

### Prerequisites

- **Rust toolchain**: Install via [rustup](https://rustup.rs/)
  - Stable toolchain for building
  - Nightly toolchain for formatting
- **Git**: For version control and submodule management
- **wasm-tools** (optional): For validating generated Wasm files
- **wabt** (optional): For viewing Wasm text format

### Setup

```sh
# Install both stable and nightly Rust
rustup install stable nightly

# Install cargo-make for build tasks (optional)
cargo install cargo-make

# Initialize submodules if not done during clone
git submodule update --init --recursive
```

### Building

```sh
# Build the project
cargo build

# Build in release mode
cargo build --release
```

## Code Style

### Formatting

We use `rustfmt` with custom settings. Before committing, format your code:

```sh
cargo +nightly fmt-stacks
```

### Linting

We use Clippy with strict settings. Check your code:

```sh
cargo clippy --no-deps --all-features --all-targets -- -D warnings
```

### Documentation

- Add doc comments (`///`) to all public items
- Use proper Markdown formatting in doc comments
- Include examples where helpful
- Run `cargo doc --no-deps` to verify documentation builds

## Testing

### Running Tests

```sh
# Run all tests
cargo test

# Run tests for a specific Clarity version
cargo test --features test-clarity-v2

# Run a specific test
cargo test test_name
```

### Test Coverage

Tests are run across multiple Clarity versions (v1-v4) in CI. Make sure your changes work across all versions.

## Pull Request Process

1. **Update documentation** if you're changing functionality
2. **Add tests** for new features or bug fixes
3. **Run the full test suite** locally before submitting
4. **Follow the PR template** provided in the repository
5. **Keep commits focused** and write clear commit messages

### Commit Message Format

We follow conventional commits:

```
type(scope): description

[optional body]
```

Types: `feat`, `fix`, `docs`, `style`, `refactor`, `test`, `chore`

Examples:
- `feat(wasm): add support for new opcode`
- `fix(linker): resolve memory alignment issue`
- `docs(readme): update installation instructions`

### Review Process

1. All PRs require at least one approval
2. CI must pass (formatting, linting, tests)
3. Maintainers may request changes
4. Once approved, a maintainer will merge your PR

## Code of Conduct

This project follows the [Contributor Covenant Code of Conduct](CODE_OF_CONDUCT.md). By participating, you agree to uphold this code.

## Questions?

If you have questions about contributing, feel free to:
- Open an issue for discussion
- Check existing issues and PRs for similar topics

Thank you for contributing to clar2wasm! 🚀
