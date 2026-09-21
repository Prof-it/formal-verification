"""Copy helpers for safe directory staging."""

import shutil
import os

def ignore_jars(dir, files):
    return [f for f in files if f.endswith('.jar')]

def copytree_symlink_safe(src, dst):
    if os.path.exists(dst):
        shutil.rmtree(dst)
    shutil.copytree(src, dst, symlinks=False, dirs_exist_ok=True, ignore=ignore_jars)
