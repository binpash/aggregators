# "cmd1 | cmd2 | cmd3" -> [cmd1, cmd2, cmd3] 
# skip empty lines and lines starting with # 

def parse_sh_file_line(line: str) -> list[str]:
    if line == "\n":
        return []

    if len(tokens := line.split("#")) > 1:
        line = tokens[0]

    commands, cur_command = [], []
    for token in line.split():
        if token == "|":
            commands.append(" ".join(cur_command))
            cur_command = []
        else:
            cur_command.append(token)
    
    if cur_command: commands.append(" ".join(cur_command))
    return commands

def parse_pipeline(pipeline_file_path: str) -> list[str]:
    pipeline: list[str] = []
    with open(pipeline_file_path, "rt") as f:
        for line in f:
            pipeline.extend(parse_sh_file_line(line))
    
    return pipeline

if __name__ == "__main__":
    import argparse
    parser = argparse.ArgumentParser()
    parser.add_argument("--input_file", "-i", type=str)
    args = parser.parse_args()

    parsed_commands = parse_pipeline(args.input_file)
    for i, command in enumerate(parsed_commands):
        print(f'Command {i}: "{command}"')
