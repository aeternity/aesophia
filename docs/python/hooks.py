import shutil

def pre_build(**kwargs):
  shutil.copy('./CHANGELOG.md', './docs')
