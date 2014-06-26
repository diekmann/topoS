#!/bin/bash
export AFP=$(readlink -f "../../thy_lib/isabelle_afp"
isabelle build -d "./" -v -l ACView
