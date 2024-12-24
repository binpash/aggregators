# "cmd1 | cmd2 | cmd3" -> [cmd1, cmd2, cmd3] 
# skip empty lines and lines starting with # 

def parse_sh_file_line(line: str) -> list[str]:
    if line == "\n":
        return []

    if len(tokens := line.split("#")) > 1:
        return []

    commands = []
    for token in line.split("|"):
        if "cat $1" in token: 
            commands.append("cat") 
        else: 
            commands.append(token.strip())
            
    return commands

def parse_pipeline(pipeline_file_path: str) -> list[str]:
    pipeline: list[str] = []
    with open(pipeline_file_path, "rt") as f:
        for line in f:
            pipeline.extend(parse_sh_file_line(line))
    return pipeline

# import argparse
# if __name__ == '__main__':
#     parser = argparse.ArgumentParser(description="Check which flags we use for sed")
#     args, unknown = parser.parse_known_args() 

#     parse_pipeline(unknown[0])
