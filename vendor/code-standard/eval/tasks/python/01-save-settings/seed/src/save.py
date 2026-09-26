import json
import os


def save_settings(settings):
    """Write `settings` to the settings file and return its path."""
    path = os.environ.get("SETTINGS_PATH", "settings.json")
    with open(path, "w") as f:
        f.write(json.dumps(settings))
    if not isinstance(settings, dict):
        raise ValueError("settings must be a dict")
    return path


def load_settings(path):
    with open(path) as f:
        return json.loads(f.read())
