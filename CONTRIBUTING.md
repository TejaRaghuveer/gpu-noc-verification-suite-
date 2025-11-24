# Contributing to NVIDIA GPU Interconnect NoC Verification

Thank you for your interest in contributing to the NVIDIA GPU Interconnect NoC Verification project! This document provides guidelines and instructions for contributing.

## Table of Contents

1. [Code of Conduct](#code-of-conduct)
2. [Getting Started](#getting-started)
3. [Development Workflow](#development-workflow)
4. [Coding Standards](#coding-standards)
5. [Testing Requirements](#testing-requirements)
6. [Commit Guidelines](#commit-guidelines)
7. [Pull Request Process](#pull-request-process)
8. [Documentation](#documentation)

## Code of Conduct

### Our Standards

- **Be respectful**: Treat all contributors with respect and professionalism
- **Be inclusive**: Welcome newcomers and help them get started
- **Be constructive**: Provide constructive feedback and suggestions
- **Be professional**: Maintain high standards of code quality and documentation

### Unacceptable Behavior

- Harassment, discrimination, or offensive comments
- Personal attacks or trolling
- Publishing others' private information without permission
- Other conduct that could reasonably be considered inappropriate

## Getting Started

### Prerequisites

Before contributing, ensure you have:

1. **Simulator Access**: VCS (Synopsys), Questa (Mentor Graphics), or Xcelium (Cadence)
2. **UVM Knowledge**: Familiarity with SystemVerilog UVM methodology
3. **Git**: Basic understanding of Git version control
4. **Environment**: Properly configured verification environment

### Setting Up Your Development Environment

1. **Clone the repository**:
   ```bash
   git clone <repository-url>
   cd noc-verification
   ```

2. **Set up the environment**:
   ```bash
   source setup.sh [vcs|questa|xcelium]
   ```

3. **Verify setup**:
   ```bash
   make check-env
   ```

4. **Run initial tests**:
   ```bash
   make compile
   make sim_simple
   ```

## Development Workflow

### Branch Strategy

- **main**: Stable, production-ready code
- **develop**: Integration branch for features
- **feature/**: Feature branches (e.g., `feature/new-test`)
- **bugfix/**: Bug fix branches (e.g., `bugfix/cov-issue`)
- **hotfix/**: Critical fixes (e.g., `hotfix/sim-crash`)

### Creating a Branch

1. **Update main branch**:
   ```bash
   git checkout main
   git pull origin main
   ```

2. **Create feature branch**:
   ```bash
   git checkout -b feature/your-feature-name
   ```

3. **Make your changes** and commit following [Commit Guidelines](#commit-guidelines)

4. **Push to remote**:
   ```bash
   git push origin feature/your-feature-name
   ```

## Coding Standards

### SystemVerilog Style Guide

#### Naming Conventions

- **Classes**: PascalCase (e.g., `noc_agent`, `noc_driver`)
- **Variables**: snake_case (e.g., `packet_count`, `data_width`)
- **Constants**: UPPER_SNAKE_CASE (e.g., `MAX_PACKET_SIZE`, `DEFAULT_TIMEOUT`)
- **Enums**: PascalCase with `_e` suffix (e.g., `packet_type_e`)
- **Interfaces**: snake_case with `_if` suffix (e.g., `noc_if`)

#### Code Formatting

- **Indentation**: 2 spaces (no tabs)
- **Line Length**: Maximum 100 characters
- **Spacing**: One space around operators, after commas
- **Braces**: Opening brace on same line for blocks

#### Example

```systemverilog
// Good
class noc_agent extends uvm_agent;
  noc_driver    driver;
  noc_monitor   monitor;
  noc_sequencer sequencer;
  
  function new(string name = "noc_agent", uvm_component parent = null);
    super.new(name, parent);
  endfunction
  
  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    // Build components
  endfunction
endclass

// Bad
class NOCAgent extends uvm_agent{
noc_driver driver;
noc_monitor monitor;
  function new(string name="noc_agent",uvm_component parent=null){
    super.new(name,parent);
  endfunction
}
```

### UVM Best Practices

1. **Use UVM Phases**: Follow standard UVM phase ordering
2. **Factory Registration**: Register all classes with UVM factory
3. **Configuration Objects**: Use `uvm_config_db` for configuration
4. **TLM Ports**: Use TLM for component communication
5. **Sequences**: Use sequences for test stimulus generation

### Documentation Standards

#### File Headers

Every file should include a header with:
- File description
- Author(s)
- Date
- Copyright notice
- Brief overview

```systemverilog
// ==============================================================================
// File: noc_agent.sv
// Description: NoC Agent Component
// Author: Your Name
// Date: 2025-01-XX
// Copyright (c) 2025 NVIDIA Corporation
// ==============================================================================
```

#### Code Comments

- **Header Comments**: Describe purpose of classes, functions, tasks
- **Inline Comments**: Explain complex logic or non-obvious code
- **TODO Comments**: Mark incomplete work: `// TODO: Add error injection`

#### Example

```systemverilog
// ==============================================================================
// Class: noc_driver
// Description: Drives transactions onto the NoC interface
// ==============================================================================
class noc_driver extends uvm_driver #(noc_packet);
  
  // Interface handle
  virtual noc_if vif;
  
  // ============================================================================
  // Function: new
  // Creates a new driver instance
  // ============================================================================
  function new(string name = "noc_driver", uvm_component parent = null);
    super.new(name, parent);
  endfunction
  
  // ============================================================================
  // Task: run_phase
  // Main driver loop - drives packets from sequencer
  // ============================================================================
  virtual task run_phase(uvm_phase phase);
    forever begin
      seq_item_port.get_next_item(req);
      drive_packet(req);
      seq_item_port.item_done();
    end
  endtask
  
endclass
```

## Testing Requirements

### Test Coverage

All contributions must include:

1. **Unit Tests**: Test individual components
2. **Integration Tests**: Test component interactions
3. **Regression Tests**: Ensure no regressions
4. **Coverage**: Maintain or improve coverage metrics

### Running Tests

```bash
# Compile
make compile

# Run specific test
make sim_simple
make sim_random SEED=42
make sim_stress

# Generate coverage report
make coverage_report
```

### Test Requirements Checklist

- [ ] All tests pass
- [ ] Coverage maintained or improved
- [ ] No linting errors
- [ ] No warnings (or documented exceptions)
- [ ] Test documentation updated

## Commit Guidelines

### Commit Message Format

Follow the conventional commits format:

```
<type>(<scope>): <subject>

<body>

<footer>
```

### Types

- **feat**: New feature
- **fix**: Bug fix
- **docs**: Documentation changes
- **style**: Code style changes (formatting, etc.)
- **refactor**: Code refactoring
- **test**: Adding or updating tests
- **chore**: Maintenance tasks

### Examples

```
feat(agent): add error injection capability

Add ability to inject errors into packets for fault testing.
Includes configuration options for error types and rates.

Closes #123
```

```
fix(driver): correct packet alignment issue

Fixed bug where packets were not properly aligned to bus
boundaries, causing simulation failures.

Fixes #456
```

### Commit Best Practices

1. **Atomic Commits**: One logical change per commit
2. **Descriptive Messages**: Clear, concise commit messages
3. **Reference Issues**: Link to related issues/PRs
4. **Test Before Commit**: Ensure tests pass before committing

## Pull Request Process

### Before Submitting

1. **Update Documentation**: Update relevant documentation
2. **Add Tests**: Include tests for new features
3. **Run Tests**: Ensure all tests pass
4. **Check Coverage**: Verify coverage metrics
5. **Update Changelog**: Add entry to CHANGELOG.md (if exists)

### PR Checklist

- [ ] Code follows style guidelines
- [ ] Self-review completed
- [ ] Comments added for complex code
- [ ] Documentation updated
- [ ] Tests added/updated
- [ ] All tests pass
- [ ] No new warnings introduced
- [ ] Coverage maintained
- [ ] Commit messages follow guidelines

### PR Description Template

```markdown
## Description
Brief description of changes

## Type of Change
- [ ] Bug fix
- [ ] New feature
- [ ] Breaking change
- [ ] Documentation update

## Testing
How was this tested?

## Checklist
- [ ] Code follows style guidelines
- [ ] Tests added/updated
- [ ] Documentation updated
- [ ] All tests pass
```

### Review Process

1. **Automated Checks**: CI/CD runs tests and checks
2. **Code Review**: At least one reviewer approval required
3. **Address Feedback**: Respond to review comments
4. **Merge**: Squash and merge when approved

## Documentation

### Required Documentation

- **README.md**: Project overview and quick start
- **Code Comments**: Inline documentation
- **Test Documentation**: Test descriptions and usage
- **API Documentation**: Component interfaces and APIs

### Documentation Standards

- Use clear, concise language
- Include code examples
- Keep documentation up to date
- Use markdown formatting consistently

## License

By contributing, you agree that your contributions will be licensed under the same license as the project (MIT License).

## Acknowledgments

Thank you for contributing to the NVIDIA GPU Interconnect NoC Verification project!

---

**Last Updated**: January 2025

