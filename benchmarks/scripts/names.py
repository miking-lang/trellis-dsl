display_names = {
    "z" : "ZipHMM",
    "pc-dense" : "Pom CPU",
    "pg-dense" : "Pom GPU",
    "tc" : "Trellis CT",
    "tr" : "Trellis RT",
    "s" : "StochHMM",
    "n" : "Native CUDA",
    "synthetic-0": "S-0",
    "synthetic-1": "S-1",
    "synthetic-2": "S-2",
    "synthetic-3": "S-3",
    "synthetic-4": "S-4",
}

def display_name(label):
    if label in display_names:
        return display_names[label]
    else:
        print(f"Could not find display name for label {label}")
        exit(1)
