import pandas as pd
import random
import matplotlib.pyplot as plt
from matplotlib.ticker import FormatStrFormatter
from matplotlib.colors import ListedColormap
from matplotlib.backends.backend_pdf import PdfPages

inputFile = "results.csv"
outputFile = "plots.pdf"

def nextColour():
    colours = ['black', 'silver', 'red', 'gold', 'sienna', 'olivedrab', 'lightseagreen', 'navy', 'blue', 'm', 'crimson', 'yellow', 'orangered', 'slateblue', 'aqua']

    for colour in colours:
        yield colour

def nextMarker():
    markers = ['.', 'v', '^', '1', '2', '8', 'p', 'P', 'x', 'D', 'd', 's']

    for marker in markers:
        yield marker

def draw(data, ax):
    ax.set_xscale('log', basex=2)
    ax.xaxis.set_major_formatter(FormatStrFormatter('%0.f'))
    ax.grid(linewidth='0.5', color='lightgray')
    ax.set_ylabel('avgTimeMs')
    ax.set_xlabel('threads')
    ax.set_xticks(data.coroutines.unique())

    colourGen = nextColour()
    markerGen = nextMarker()
    for graphName in data.graphName.unique():
        genColour = next(colourGen)
        genMarker = next(markerGen)
        resParallel = data[(data.graphName == graphName) & (data.coroutines != 0)]
        print(resParallel.coroutines)
        ax.plot(resParallel.coroutines, resParallel.executionTimeAvgMs, label="graphName={}".format(graphName), color=genColour, marker=genMarker)
        #         sentAx.errorbar(x=res.coroutines, y=res.executionTimeAvgMs, yerr=res.executionTimeStdMs, solid_capstyle='projecting', capsize=5)
        resSequential = data[(data.graphName == graphName) & (data.coroutines == 0)]
        resSequential = pd.concat([resSequential.executionTimeAvgMs]*(len(resParallel.coroutines)))
        ax.plot(resParallel.coroutines, resSequential, linestyle='--',label="graphName={}-sequential".format(graphName), color=genColour)

def genFile(pdf):
    data = pd.read_table(inputFile, sep=",")
    fig, ax = plt.subplots(nrows=1, ncols=1, figsize=(20, 20))
    draw(data, ax)
    lines, labels = ax.get_legend_handles_labels()
    fig.legend(lines, labels, loc='upper center', borderpad=0, ncol=4, frameon=False, borderaxespad=4, prop={'size': 8})

    plt.tight_layout(pad=12, w_pad=2, h_pad=1)
    pdf.savefig(bbox_inches='tight')

with PdfPages(outputFile) as pdf:
    genFile(pdf)