import pandas as pd
import matplotlib.pyplot as plt
from matplotlib.ticker import FormatStrFormatter
from matplotlib.backends.backend_pdf import PdfPages

inputFile = "results.csv"
outputFile = "in-memory-chat-plots.pdf"

colours = ['black', 'silver', 'red', 'gold', 'sienna', 'olivedrab', 'lightseagreen', 'navy', 'blue', 'm', 'crimson', 'yellow', 'orangered', 'slateblue', 'aqua']
markers = ['.', 'v', '^', '1', '2', '8', 'p', 'P', 'x', 'D', 'd', 's']

def next_colour():
    i = 0
    while True:
        yield colours[i % len(colours)]
        i += 1

def next_marker():
    i = 0
    while True:
        yield markers[i % len(markers)]
        i += 1

def draw(data, bench_mode, avg_work, users, max_friends, sent_ax):
    sent_ax.set_xscale('log', basex=2)
    sent_ax.xaxis.set_major_formatter(FormatStrFormatter('%0.f'))
    sent_ax.grid(linewidth='0.5', color='lightgray')
    sent_ax.set_ylabel('msgSent / ms')
    sent_ax.set_xlabel('threads')
    sent_ax.set_xticks(data.threads.unique())

    colour_gen = next_colour()
    marker_gen = next_marker()
    for channel in data.channel.unique():
        for dispatcherType in data.dispatcherType.unique():
            gen_colour = next(colour_gen)
            gen_marker = next(marker_gen)
            res = data[(data.benchmarkMode == bench_mode) & (data.averageWork == avg_work) & (data.userCount == users) & (data.maxFriendsPercentage == max_friends) & (data.channel == channel) & (data.dispatcherType == dispatcherType)].sort_values(by=['threads'])
            sent_ax.plot(res.threads, res.avgSentMessages, label="channel={},dispatcher={}".format(channel, dispatcherType), color=gen_colour, marker=gen_marker)
            # sent_ax.errorbar(x=res.threads, y=res.avgSentMessages, yerr=res.stdSentMessages, solid_capstyle='projecting', capsize=5)

def genFile(pdf):
    data = pd.read_table(inputFile, sep=",")
    for benchMode in data.benchmarkMode.unique():
        for avgWork in data.averageWork.unique():
            for users in data.userCount.unique():
                for maxFriends in data.maxFriendsPercentage.unique():
                    fig, ax = plt.subplots(nrows=1, ncols=1, figsize=(20, 20))
                    draw(data, benchMode, avgWork, users, maxFriends, ax)
                    lines, labels = ax.get_legend_handles_labels()
                    fig.suptitle("benchMode={},avgWork={},users={},maxFriends={}".format(benchMode, avgWork, users, maxFriends), fontsize=12, y=1)
                    fig.legend(lines, labels, loc='upper center', borderpad=0, ncol=4, frameon=False, borderaxespad=4, prop={'size': 8})

                    plt.tight_layout(pad=12, w_pad=2, h_pad=1)
                    pdf.savefig(bbox_inches='tight')

with PdfPages(outputFile) as pdf:
    genFile(pdf)