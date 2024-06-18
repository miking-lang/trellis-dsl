display_names = {
    "z" : "ZipHMM",
    "pc" : "Pom CPU",
    "pg" : "Pom GPU",
    "tc" : "Trellis CT",
    "tr" : "Trellis RT",
    "s" : "StochHMM",
    "n" : "Native CUDA"
}

def display_name(label):
    if label in display_names:
        return display_names[label]
    else:
        print(f"Could not find display name for label {label}")
        exit(1)
