# Contributing to æSophia

## Checklist For Creating New Pull Requests

### Documentation

- Update [Changelog](CHANGELOG.md) for all PRs.
- If the PR introduces a new feature that is relevant to the users of the language, the [Sophia Features Documentation](doc/sophia_features.md) should be updated to describe the new feature.
- If the PR introduces new syntax (e.g. changes in [aeso_syntax.erl](src/aeso_syntax.erl), [aeso_scan.erl](src/aeso_scan.erl), or [aeso_parser.erl](src/aeso_parser.erl)), the [Sophia Syntax Documentation](doc/sophia_syntax.md) should be updated to include the new syntax.
- If the PR introduces a new library, the new library's public interface should be fully documented in the [Sophia Standard Library Documentation](doc/sophia_stdlib.md).

### Tests

- If the PR introduces new syntax (e.g. changes in [aeso_syntax.erl](src/aeso_syntax.erl), [aeso_scan.erl](src/aeso_scan.erl), or [aeso_parser.erl](src/aeso_parser.erl)), the contract [all_syntax.aes](test/contracts/all_syntax.aes) should be updated to include the new syntax.
- If the PR fixes a bug, the code that replicates the bug should be added as a new passing test contract.