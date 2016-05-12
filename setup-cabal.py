#!/usr/bin/env python2

import os
import subprocess

def main():
    # directories that contain packages
    dirs = [".", "libs"]

    # create the sandbox
    print_run(["cabal", "sandbox", "init"])

    # for each package (i.e. a directory that contains a *.cabal file)
    # in the given directories, add-source and tell cabal to use the
    # main sandbox for it.
    for dir in dirs:
        for subdir in get_subdirs(dir):
            if any(file.endswith(".cabal") for file in get_files(subdir)):
                print_run(["cabal", "sandbox", "add-source", subdir])
                cwd = os.getcwd()
                cd_run(subdir, lambda: print_run(["cabal", "sandbox", "init", \
                    "".join(["--sandbox=", cwd, os.path.sep, ".cabal-sandbox"])]))

def cd_run(path, fun):
    """cd into the given path, run the function and cd back."""
    # store current directory
    owd = os.getcwd()

    # cd into given path
    print("cd " + path)
    os.chdir(path)

    # run the function
    fun()

    # cd back
    print("cd -")
    os.chdir(owd)

def print_run(cmd):
    """Print out the command and then run it."""
    print(" ".join(cmd))
    subprocess.call(cmd)

def get_subdirs(dir):
    """Get the sub-directories of a given directory."""
    return [os.path.join(dir,entry) for entry in os.listdir(dir) \
            if os.path.isdir(os.path.join(dir,entry))]

def get_files(dir):
    """Get the files in a given directory."""
    return [os.path.join(dir,entry) for entry in os.listdir(dir) \
            if os.path.isfile(os.path.join(dir,entry))]

main()
