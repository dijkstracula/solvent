from solvent.env import ScopedEnv


def test_env_immutable():
    original_env = ScopedEnv.empty()
    original_env.add("x", 0)
    original_env.add("y", 1)

    assert original_env == ScopedEnv.empty()


def test_env_scopes():
    original = ScopedEnv.empty()
    original = original.push_scope()
    original = original.add("x", 0)
    original = original.add("y", 0)
    assert list(original.items()) == [("x", 0), ("y", 0)]
    original = original.pop_scope()
    assert original == ScopedEnv.empty()
