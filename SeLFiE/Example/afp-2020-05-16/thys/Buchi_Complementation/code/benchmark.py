#!/usr/bin/python

import sys, random, subprocess

def write(path, text):
	f = open(path, "w")
	f.write(text)
	f.close()

def generate_automaton():
	seed = random.randrange(0x10000)
	result = subprocess.run(["randaut", "--seed={}".format(seed), "--ba", "--states=20", "a", "b", "c", "d"], stdout = subprocess.PIPE, text = True)
	return result.stdout
def generate_formula():
	seed = random.randrange(0x10000)
	result = subprocess.run(["randltl", "--seed={}".format(seed), "4"], stdout = subprocess.PIPE, text = True)
	return result.stdout
def translate_formula(formula):
	result = subprocess.run(["ltl2tgba", "--ba", formula], stdout = subprocess.PIPE, text = True)
	return result.stdout

if sys.argv[1] == "complement_automaton":
	write("a.hoa", generate_automaton())
	subprocess.run(["./Autool", "complement_quick", "a.hoa", "c.txt"])
if sys.argv[1] == "complement_formula":
	write("formula.hoa", translate_formula(generate_formula()))
	subprocess.run(["./Autool", "complement_quick", "formula.hoa", "formula_complement.txt"])
# TODO: doesn't work if alphabets aren't equal
if sys.argv[1] == "equivalence":
	while True:
		write("a.hoa", translate_formula(generate_formula()))
		write("b.hoa", translate_formula(generate_formula()))
		result = subprocess.run(["./Autool", "equivalence", "a.hoa", "b.hoa"], stdout = subprocess.PIPE, text = True)
		if result.stdout == "true": break
