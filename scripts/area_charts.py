import argparse
import pandas as pd
import matplotlib.pyplot as plt

# Parse command-line arguments
parser = argparse.ArgumentParser(description="Plot Area pie chart")
parser.add_argument("--report_file",
                    help="Area report of LEN5")
parser.add_argument("--chart_file",
                    help="Output PNG chart file")

args = parser.parse_args()

# Use LaTeX to render text
# plt.rc("text", usetex=True)
plt.rc("font", family="sans-serif")

# Initialization
report_file = args.report_file
chart_file = args.chart_file

data = {
    'Submodule': [],
    'Area': [],
    'Utilization Percentage': [],
    'Combinational Area': [],
    'Non-Combinational Area': []
}

# Parse Area report
with open(report_file, 'r') as fp:
    lines = fp.readlines()
    area = {}
    for line in lines:
        if ('/' in line or ':' in line):
            continue

        parts = line.split()

        if (len(parts) != 7):
            continue
        
        if (parts[0][0] != 'u'): # Skip non-submodule lines
            continue
            
        if (float(parts[2]) < 1): # Skip submodules with less than 1% utilization
            continue
        
        data['Submodule'].append(str(parts[0]))
        data['Area'].append(float(parts[1]))
        data['Utilization Percentage'].append(float(parts[2]))
        data['Combinational Area'].append(float(parts[3]))
        data['Non-Combinational Area'].append(float(parts[4]))

df = pd.DataFrame(data)
print(df)

colors = ["#6d1a3680", "#6d1a36c0", "#6d1a36ff", "#00748080", "#007480c0", "#007480ff"]
df_bars = df[["Submodule", "Utilization Percentage"]]

df_bars.plot(kind="pie", rot=0, y='Utilization Percentage', x='Submodule', title="Area Utilization per Submodule", figsize=(12, 5), color=colors)

# Draw horizontal grid only
plt.gca().yaxis.grid(True)

# Set suptitle
plt.suptitle("LEN5 Processor IPC Improvement", fontweight="bold", fontsize="x-large", color="#3d3d3dff")

# Superpose an horizontal line at y=1 with label "CPU"
# plt.axhline(y=1, color="#3d3d3dff", linestyle="--")
# plt.text(-0.62, 2, "CPU", color="#3d3d3dff", rotation=0, fontsize="small")

# Set Y max value
# plt.gca().set_ylim([0, 1]) //TODO uncomment this if just IPC

# Add 'x' to the y-axis step labels
# plt.gca().yaxis.set_major_formatter(lambda x, pos: str(int(x)) + "x")

# Set legend titles
plt.gca().set_title(plt.gca().get_title(), fontsize="large", color="#3d3d3dff")
plt.gca().legend(title="Processor")
# plt.gca().set_xlabel(plt.gca().get_xlabel(), fontweight="bold")
# plt.gca().set_ylabel(plt.gca().get_ylabel(), fontweight="bold")

plt.savefig(chart_file, dpi=600, bbox_inches="tight")
