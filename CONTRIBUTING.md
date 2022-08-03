# Contributing to æSophia

## Checklist For Creating New Pull Requests

The following points should be considered before creating a new PR to the Sophia compiler.

### Documentation

- The [Changelog](CHANGELOG.md) file should be updated for all PRs.
- If a PR introduces a new feature that is relevant to the users of the language, the [Sophia Features Documentation](docs/sophia_features.md) should be updated to describe the new feature.
- If a PR introduces new syntax (e.g. changes in [aeso_syntax.erl](src/aeso_syntax.erl), [aeso_scan.erl](src/aeso_scan.erl), or [aeso_parser.erl](src/aeso_parser.erl)), the [Sophia Syntax Documentation](docs/sophia_syntax.md) should be updated to include the new syntax.
- If a PR introduces a new library, the public interface of the new library should be fully documented in the [Sophia Standard Library Documentation](docs/sophia_stdlib.md).

### Tests

- If a PR introduces new syntax (e.g. changes in [aeso_syntax.erl](src/aeso_syntax.erl), [aeso_scan.erl](src/aeso_scan.erl), or [aeso_parser.erl](src/aeso_parser.erl)), the contract [all_syntax.aes](test/contracts/all_syntax.aes) should be updated to include the new syntax.
- If a PR fixes a bug, the code that replicates the bug should be added as a new passing test contract.
- If a PR introduces a new feature, add tests for both successful and failing usage of that feature. In order to run the entire compilation pipeline and to avoid erroring during intermediate steps, failing tests should not be mixed with the successful ones.

### Source Code

- If a PR introduces new syntax (e.g. changes in [aeso_syntax.erl](src/aeso_syntax.erl), [aeso_scan.erl](src/aeso_scan.erl), or [aeso_parser.erl](src/aeso_parser.erl)), the following code should be updated to handle the new syntax:
    - The function `aeso_syntax_utils:fold/4` in the file [aeso_syntax_utils.erl](src/aeso_syntax_utils.erl).
    - Any related pretty printing function in the file [aeso_pretty.erl](src/aeso_pretty.erl), depending on the type of the newly added syntax.
