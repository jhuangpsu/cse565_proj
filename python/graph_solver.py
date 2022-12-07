from graph import *
from graph_helper import *
from constants import *
from input_output import *
from solver_algorithms import *

"""
This file extracts leafy spanning trees from graphs, for part 2 of the MLST project.
"""

# Takes in files from default input, solves them using all algorithms, logs their
# performance onto the console, writes the solutions into a file, and merges the
# solutions from this run with the solutions from the existing file to generate
# the best solution thus far
def do_everything():
	graphs = input_graphs_from_file(ALL_GRAPHS_INPUT)
	trees = find_leafy_spanning_trees(graphs)
	output_trees_to_new_file(trees, TEMPORARY_TREES_OUTPUT)
	merge_solutions(ALL_TREES_OUTPUT, TEMPORARY_TREES_OUTPUT, MERGED_OUTPUT)


# Takes a list of graphs and returns the leafiest spanning tree we can find
# by running them through all of our algorithms
def find_leafy_spanning_trees(graphs):

	# Initialize our graph-tree pairs
	our_graphs = input_graphs_from_file(OUR_GRAPHS)
	our_trees = input_graphs_from_file(OUR_TREES)

	# Initialize manually-solved graph-tree pairs
	manually_solved_graphs = input_graphs_from_file(MANUALLY_SOLVED_GRAPHS)
	manually_solved_trees = input_graphs_from_file(MANUALLY_SOLVED_TREES)

	leafy_spanning_trees = []

	for i in range(len(graphs)):
		best_tree = find_leafy_spanning_tree(graphs[i], i, our_graphs, our_trees, manually_solved_graphs, manually_solved_trees)
		leafy_spanning_trees.append(best_tree)

	return leafy_spanning_trees


# Takes a graph and returns the leafiest spanning tree we can find by running
# it through all of our algorithms
# For best results, also provide our own graph-tree pairs and manually-solved pairs
def find_leafy_spanning_tree(graph, graph_number=0, our_graphs=[], our_trees=[], manually_solved_graphs=[], manually_solved_trees=[]):

	# Maintain a record of bests so far
	best_tree = None
	best_leaf_count = 0
	best_algorithm = ''

	# Test for graph generated by us
	for i in range(len(our_graphs)):
		if are_equivalent_graphs(graph, our_graphs[i]):
			our_trees[i].search()
			best_tree = our_trees[i]
			best_leaf_count = our_trees[i].num_leaves
			best_algorithm = 'our own solution'

	# Test for line
	if is_line(graph):
		print('Best solution for instance ' + str(graph_number) + ':\tLeaves: ' + str(len(get_leaves(graph))) + '\t/\t' + str(len(get_nodes(graph))) + '\tAlgorithm: detected line')
		return graph

	# Test for tree
	if is_tree(graph):
		print('Best solution for instance ' + str(graph_number) + ':\tLeaves: ' + str(len(get_leaves(graph))) + '\t/\t' + str(len(get_nodes(graph))) + '\tAlgorithm: detected tree')
		return graph

	# Test for small input size
	if len(get_edges(graph)) < SMALL_NUMBER_OF_EDGES:
		for i in range(len(manually_solved_graphs)):
			if are_equivalent_graphs(graph, manually_solved_graphs[i]):
				solved_tree = manually_solved_trees[i]
				solved_tree.search()
				if solved_tree.num_leaves > best_leaf_count:
					best_tree = solved_tree
					best_leaf_count = solved_tree.num_leaves
					best_algorithm = 'manually solved'

	# Try all algorithms and record the best one
	for algorithm_name, algorithm in ALGORITHMS:
		tree = algorithm(graph)
		tree.search()

		if tree.num_leaves > best_leaf_count:
			best_tree = tree
			best_leaf_count = tree.num_leaves
			best_algorithm = algorithm_name

	# Log the best solution
	print('Best solution for instance ' + str(graph_number) + ':\tLeaves: ' + str(best_leaf_count) + '\t/\t' + str(len(get_nodes(graph))) + '\tAlgorithm: ' + best_algorithm)

	return best_tree


if __name__ == '__main__':
    do_everything()

