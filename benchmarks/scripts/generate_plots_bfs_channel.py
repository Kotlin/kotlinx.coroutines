# To run this script run the command 'python3 scripts/generate_plots_bfs_channel.py' in the benchmarks/ folder or
# 'python3 generate_plots_bfs_channel.py' in the benchmarks/scripts/ folder

import pandas as pd
import matplotlib.pyplot as plt
from matplotlib.ticker import FormatStrFormatter

input_file = "out/results_bfs_channel.csv"
output_file = "out/bfs-channel.svg"

markers = ['.', 'v', '^', '1', '2', '8', 'p', 'P', 'x', 'D', 'd', 's']
colours = ['red', 'gold', 'sienna', 'olivedrab', 'lightseagreen', 'navy', 'blue', 'm', 'crimson', 'yellow', 'orangered', 'slateblue', 'aqua', 'black', 'silver']

def next_colour():
    for colour in colours:
        yield colour

def next_marker():
    for marker in markers:
        yield marker

def draw(data, plt):
    plt.xscale('log', basex=2)
    plt.gca().xaxis.set_major_formatter(FormatStrFormatter('%0.f'))
    plt.grid(linewidth='0.5', color='lightgray')
    plt.ylabel('speed up (parallel time / sequential time)')
    plt.xlabel('parallelism')
    plt.xticks(data.parallelism.unique())

    colour_gen = next_colour()
    marker_gen = next_marker()
    for graphName in data.graphName.unique():
        gen_colour = next(colour_gen)
        gen_marker = next(marker_gen)
        res_parallel = data[(data.graphName == graphName) & (data.parallelism != 0)]
        res_sequential_time = data[(data.graphName == graphName) & (data.parallelism == 0)].executionTimeAvgMs.unique()
        plt.plot(res_parallel.parallelism, res_parallel.executionTimeAvgMs / res_sequential_time,
                label="graphName={}".format(graphName), color=gen_colour, marker=gen_marker, linewidth=2.2)

data = pd.read_csv(input_file, sep=",")
plt.rcParams.update({'font.size': 15})
plt.figure(figsize=(15, 12.5))
draw(data, plt)
plt.legend(loc='upper center', borderpad=0, bbox_to_anchor=(0.5, 1.2), ncol=2, frameon=False, borderaxespad=2, prop={'size': 15})
plt.tight_layout(pad=12, w_pad=2, h_pad=1)
plt.savefig(output_file, bbox_inches='tight')