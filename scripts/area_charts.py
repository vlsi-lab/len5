import argparse
import pandas as pd
import matplotlib.pyplot as plt

# Parse command-line arguments
parser = argparse.ArgumentParser(description="Plot Area pie chart")
parser.add_argument("--report_file",
                    help="Area report of LEN5")
parser.add_argument("--chart_file",
                    help="Output PNG chart file")
parser.add_argument("--submodules",
                    help="Submodule file")

args = parser.parse_args()

# Use LaTeX to render text
# plt.rc("text", usetex=True)
plt.rc("font", family="sans-serif")

# Initialization
report_file = args.report_file
chart_file = args.chart_file
submodule_file = args.submodules

if (args.submodules is None):
    print("Submodules file is required.")
    exit(1)

data = {
    'Submodule': [],
    'Area': [],
    'Utilization Percentage': [],
    'Combinational Area': [],
    'Non-Combinational Area': []
}
with open(submodule_file, 'r') as subfp:

    # Parse Submodule file
    sublines = subfp.readlines()
    submodules = []
    for line in sublines:
        if (line[0] == '#'):
            continue
        submodules.append(line.strip())

    # Parse Area report
    with open(report_file, 'r') as fp:
        lines = fp.readlines()
        area = {}
        for line in lines:
            parts = line.split()
            
            if (len(parts) != 7):
                continue

            if (parts[0] not in submodules):
                continue
               
            # Re-name submodule name to keep last u_... part
            parts[0] = parts[0].split('/')[-1]
            parts[0] = parts[0].split('u_')[-1]

            data['Submodule'].append(str(parts[0]))
            data['Area'].append(float(parts[1]))
            data['Utilization Percentage'].append(float(parts[2]))
            data['Combinational Area'].append(float(parts[3]))
            data['Non-Combinational Area'].append(float(parts[4]))

df = pd.DataFrame(data)
print(df)

colors = ["#6d1a3680", "#6d1a36c0", "#6d1a36ff", "#00748080", "#007480c0", "#007480ff"]
df_bars = df[["Submodule", "Utilization Percentage"]]

ax = df_bars.plot(kind="pie", y='Utilization Percentage', labels=df_bars['Submodule'], title="Area Utilization per Submodule", figsize=(12, 5), legend=False, autopct='%1.1f%%')

ax.set_ylabel("")

# Draw horizontal grid only
plt.gca().yaxis.grid(True)

# Set suptitle
plt.suptitle("LEN5 Area Partitions", fontweight="bold", fontsize="x-large", color="#3d3d3dff")

# Set legend titles
plt.gca().set_title(plt.gca().get_title(), fontsize="large", color="#3d3d3dff")
plt.gca().set_xlabel(plt.gca().get_xlabel(), fontweight="bold")
plt.gca().set_ylabel(plt.gca().get_ylabel(), fontweight="bold")

plt.savefig(chart_file, dpi=600, bbox_inches="tight")
