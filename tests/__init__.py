import pytest

# Stack Overflow: https://stackoverflow.com/questions/41522767/pytest-assert-introspection-in-helper-function
# Pytest rewrites the AST so that standard python assert statements give more information
# However, it only does this for files that have tests in them. We need to register other files
# explicitly. The following line does just that.
pytest.register_assert_rewrite("tests.utils")
