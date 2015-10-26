#!/usr/bin/env python

from __future__ import print_function
from sys import argv
import os
from os import system
import re
import string
import random

clang_path = os.environ.get('CLANG_PATH', "")
if clang_path :
    clang_path += "/"

src_pattern = re.compile(".*\.(cc|c|cxx|cpp)$")
args = [clang_path + "clang", "-emit-ast"]
files = []
call_args = []

xtu_dir = os.environ.get('OUT_DIR', "")

random_magic_set = string.ascii_lowercase + string.digits
random_magic = ''.join(random.sample(random_magic_set * 6, 6))
os.environ['XTU_MAGIC'] = random_magic

def get_ast_path(f):
    return os.path.join(xtu_dir,
                        os.path.join("/ast/" + random_magic,
                                     os.path.realpath(f)[1:] + ".ast")[1:])

# FIXME: More precise filter is needed here.
for ind in range(1, len(argv)) :
    arg = argv[ind]
    if src_pattern.match(arg) :
        files.append(arg)
    else :
        call_args.append(arg)
call_args.append("-w")
for f in files:
    try:
        os.makedirs(os.path.dirname(get_ast_path(f)))
    except OSError:
        pass

rets = [system(' '.join(args + call_args + [f, "-o", get_ast_path(f) ])) for f in files]
ret = 0
if len(filter(lambda x: x != 0, rets)) != 0 :
    ret = 1

if len(files) > 0:
    if system(' '.join([clang_path + "clang-func-mapping"] + files + ["--"] + call_args)) != 0 :
        ret = 1

exit(ret)
