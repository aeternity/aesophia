import glob
import shutil

def pre_build(**kwargs):
  for file in glob.glob('../docs/*.md'):
    shutil.copy(file, 'docs')
  shutil.copy('../CHANGELOG.md', 'docs')
