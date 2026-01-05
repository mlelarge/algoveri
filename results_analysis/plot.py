import matplotlib.pyplot as plt

# Updated Data with "Basic / Structural" label
labels = [
    'DS: Basic / Structural\n(Stack, Queue, Trie, BST)',   # Balanced at Top-Right
    'DS: Complex Invariant\n(Heap, RB-Tree, TST, ...)',         # Balanced at Top-Left
    'Graphs', 
    'Math', 
    'DP & Greedy', 
    'Sorting', 
    'String'
]

counts = [15, 16, 13, 11, 10, 7, 5]

# Colors: Preserving the "Blue Split" for Data Structures
colors = ['#a0cbe8', '#4e79a7', '#e15759', '#76b7b2', '#59a14f', '#edc948', '#b07aa1']

fig, ax = plt.subplots(figsize=(9, 7), subplot_kw=dict(aspect="equal"))

# startangle=10 positions zthe two largest slices (DS) at the top corners
# This balances the long text labels between Left and Right margins.
wedges, texts, autotexts = ax.pie(counts, labels=labels, autopct='%1.0f%%', 
                                  startangle=20, colors=colors, pctdistance=0.85,
                                  wedgeprops=dict(width=0.4, edgecolor='w'))

# Styling for publication quality
plt.setp(texts, size=14, weight="bold")
plt.setp(autotexts, size=20, weight="bold", color="white")

# Center Summary Text
ax.text(0, 0, "AlgoVeri\n77 Problems\n(Balanced Difficulty)", 
        ha='center', va='center', fontsize=18, weight='bold')

#ax.set_title("Benchmark Distribution\n(Explicit Difficulty Split)", fontsize=14, weight="bold")

plt.tight_layout()
plt.savefig("results_analysis/algoveri_distribution_balanced.png")
plt.show()