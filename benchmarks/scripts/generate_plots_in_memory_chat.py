# To run this script run the command 'python3 scripts/generate_plots_in_memory_chat.py' in the /benchmarks folder

import pandas as pd
import matplotlib.pyplot as plt
from matplotlib.ticker import FormatStrFormatter
from matplotlib.backends.backend_pdf import PdfPages
import datetime

input_file = "out/results_in_memory_chat.csv"
output_file = "out/in-memory-chat.pdf"

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

def draw(data, users, max_friends, ax_arr):
    flatten_ax_arr = ax_arr.flatten()
    for ax in flatten_ax_arr:
        ax.set_xscale('log', basex=2)
        ax.xaxis.set_major_formatter(FormatStrFormatter('%0.f'))
        ax.grid(linewidth='0.5', color='lightgray')
        ax.set_ylabel('msgSent / ms')
        ax.set_xlabel('threads')
        ax.set_xticks(data.threads.unique())

    i = 0
    for dispatcher_type in data.dispatcherType.unique():
        for avg_work in data.averageWork.unique():
            flatten_ax_arr[i].set_title("dispatcherType={},avgWork={}".format(dispatcher_type, avg_work))
            colour_gen = next_colour()
            marker_gen = next_marker()
            for channel in data.channel.unique():
                gen_colour = next(colour_gen)
                gen_marker = next(marker_gen)
                res = data[(data.dispatcherType == dispatcher_type) & (data.averageWork == avg_work) & (data.userCount == users) & (data.maxFriendsPercentage == max_friends) & (data.channel == channel)]
                flatten_ax_arr[i].plot(res.threads, res.avgSentMessages, label="channel={}".format(channel), color=gen_colour, marker=gen_marker)
#                 flatten_ax_arr[i].errorbar(x=res.threads, y=res.avgSentMessages, yerr=res.stdSentMessages, label="channel={}".format(channel), solid_capstyle='projecting', color=gen_colour, marker=gen_marker, capsize=5)
            i += 1

def genFile(pdf):
    data = pd.read_csv(input_file, sep=",")
    for users in data.userCount.unique():
        for max_friends in data.maxFriendsPercentage.unique():
            fig, ax_arr = plt.subplots(nrows=2, ncols=2, figsize=(20, 15))
            draw(data, users, max_friends, ax_arr)
            lines, labels = ax_arr[0, 0].get_legend_handles_labels()
            fig.suptitle("users={},maxFriends={}".format(users, max_friends), fontsize=12, y=1)
            fig.legend(lines, labels, loc='upper center', borderpad=0, ncol=4, frameon=False, borderaxespad=4, prop={'size': 8})

            plt.tight_layout(pad=12, w_pad=2, h_pad=1)
            pdf.savefig(bbox_inches='tight')

with PdfPages(output_file) as pdf:
    genFile(pdf)