import os
import argparse
import pandas as pd


def has_requires(data_subset, test_file):
    program_path = get_program_path(data_subset, test_file)
    with open(program_path, "r") as file:
        body = file.read()
    return "requires" in body


def has_ensures(data_subset, test_file):
    program_path = get_program_path(data_subset, test_file)
    with open(program_path, "r") as file:
        body = file.read()
    return "ensures" in body


def count_char(data_subset, test_file):
    program_path = get_program_path(data_subset, test_file) 
    with open(program_path, "r") as file:
        body = file.read()
    return len(body)


def count_hint_char(data_subset, test_file):
    program_path = get_program_path(data_subset, test_file)
    hint_char_count = 0
    hint_keywords = ["assert", "invariant", "decreases"]

    with open(program_path, "r") as file:
        lines = file.readlines()

    for line in lines:
        stripped_line = line.strip()
        if any(stripped_line.startswith(keyword) for keyword in hint_keywords):
            hint_char_count += len(stripped_line)  # Count characters in this line
        else:
            continue
    
    return hint_char_count


def count_lemma(data_subset, test_file):
    program_path = get_program_path(data_subset, test_file)
    with open(program_path, "r") as file:
        body = file.read()
    return body.count("lemma")


def count_function(data_subset, test_file):
    program_path = get_program_path(data_subset, test_file)
    with open(program_path, "r") as file:
        body = file.read()
    return body.count("function")


def count_method(data_subset, test_file):
    program_path = get_program_path(data_subset, test_file)
    with open(program_path, "r") as file:
        body = file.read()
    return body.count("method")


def verifies_without_hints(test_file):
    with open("verify_without_hints_files.txt", "r") as file:
        auto_verifying_files = file.read().splitlines()
    test_file = test_file.replace("_no_hints", "")
    return test_file in auto_verifying_files


def get_program_path(data_subset, test_file):
    if data_subset == "ground_truth":
        return f"../dataset/ground_truth/{test_file}"
    elif data_subset == "hints_removed":
        return f"../dataset/hints_removed/{test_file}"
    else:
        raise ValueError("Invalid data subset: Data subset must be 'ground_truth' or 'hints_removed'")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Collect metadata of pa Dafny program")
    parser.add_argument("--data_subset", type=str, required=True, help="Data subset (ground_truth / hints_removed)")
    args = parser.parse_args()

    for test_file in os.listdir(f"../dataset/{args.data_subset}"):
        requires_exists = has_requires(args.data_subset, test_file)
        ensures_exists = has_ensures(args.data_subset, test_file)
        num_chars = count_char(args.data_subset, test_file)
        num_hint_char = count_hint_char(args.data_subset, test_file)
        num_lemma = count_lemma(args.data_subset, test_file)
        num_function = count_function(args.data_subset, test_file)
        num_method = count_method(args.data_subset, test_file)
        auto_verify = verifies_without_hints(test_file)

        metadata_file = f"{args.data_subset}_metadata.csv"
        new_metadata = {'test_file': test_file,
                        'has_requires': requires_exists,
                        'has_ensures': ensures_exists,
                        '#_char': num_chars,
                        '#_hint_char': num_hint_char,
                        '#_lemma': num_lemma,
                        '#_function': num_function,
                        '#_method': num_method,
                        'verifies_without_hints': auto_verify}
        df = pd.read_csv(metadata_file)
        df = df._append(new_metadata, ignore_index=True)
        df.to_csv(metadata_file, index=False)
    
    df = pd.read_csv(metadata_file)
    df = df.sort_values(by='test_file')
    df.insert(0, 'test_ID', range(0, 0 + len(df)))
    df['test_ID'] = df['test_ID'].apply(lambda x: f"{x:03}")
    df.to_csv(metadata_file, index=False)
