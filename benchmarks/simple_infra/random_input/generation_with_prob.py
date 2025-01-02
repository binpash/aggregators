import string, random
from  collections import defaultdict
from math import floor, sqrt, ceil 
import numpy as np

class RandomGeneratorProb(): 
    def __init__(self, write_to_: str, file_size_target_: int, file_line_target_:int, 
                identical_word_prob_: float, identical_line_len_prob_: float): 
        if identical_word_prob_ < 0 or identical_word_prob_ > 1: 
            raise ValueError("probability must be in range [0,1]", identical_word_prob_)
        
        if identical_line_len_prob_ < 0 or identical_line_len_prob_ > 1: 
            raise ValueError("probability must be in range [0,1]", identical_line_len_prob_)
        
        if file_line_target_ > file_size_target_: 
            raise ValueError("cannot have more lines than byte", identical_word_prob_)
        
        self.write_to = write_to_
        self.file_size_target = file_size_target_ 
        self.file_line_target = file_line_target_
        self.i_word_prob = identical_word_prob_
        self.i_line_len_prob = identical_line_len_prob_
        self.char_pool = string.ascii_lowercase + string.ascii_uppercase + string.digits + string.punctuation
        
    def generate(self): 
        len_distribution = self.generate_sentence_len_distribution(self.i_line_len_prob, self.file_size_target, self.file_line_target)
        text = self.generate_text_with_prob(self.i_word_prob, len_distribution)
        self.shuffle_text(text)
        if self.write_to != "": 
            self.write_text_to_file(text)
        return text 

    # Probability Functions
    def generate_sentence_len_distribution(self, identical_len_prob: int, total_bytes: int, total_lines: int) -> list[int]:     
            num_of_same_len = ceil(total_lines * identical_len_prob)
            num_of_uniq_len = total_lines - num_of_same_len
            
            distribution = [0] * total_lines
            used_line_len = defaultdict(int)
            bytes_to_distribute = total_bytes
            
            # Assign lines with same line length one identical line length. 
            identical_byte_val = random.randint(1, floor(total_bytes / total_lines))
            for idx in range(0, num_of_same_len): 
                distribution[idx] = identical_byte_val
                bytes_to_distribute -= identical_byte_val
                used_line_len[identical_byte_val] += 1 
            
            # Assign rest of the lines with unique line lengths, to its best capability. 
            # Randomly sample dividers in range of all bytes to distribute;  
            # Each chunk, separated by divider, is length for one line. 
            curr_sentence_idx = num_of_same_len
            lengths = [num for num in range(1, bytes_to_distribute)]
            dividers = sorted(random.sample(lengths, num_of_uniq_len - 1))
            r_end = bytes_to_distribute
            l_end_idx = len(dividers) - 1
            while l_end_idx > -1: 
                l_end = dividers[l_end_idx]
                curr_len = r_end - l_end
                
                # Reduce repeats by summing with next chunk and 
                # randomly generate new values. 
                if curr_len in distribution and l_end_idx > 1: 
                    next_l_end_idx = l_end_idx - 1
                    sum_with_next = r_end - dividers[next_l_end_idx]
                    print(sum_with_next, "sum ")
                    new_len_1 = random.randint(1, sum_with_next - 1)
                    curr_len = new_len_1
                    l_end = r_end - new_len_1
                
                distribution[curr_sentence_idx] = curr_len 
                used_line_len[curr_len] += 1 
                r_end = l_end
                l_end_idx -= 1 
                curr_sentence_idx += 1
            
            distribution[-1] = r_end 
           
            # Gather actual distribution data and ensure distribution of lengths add up to total bytes. 
            total_repeated_line_length = sum([line for line in used_line_len.values() if line > 1])
            print("splitting into:", total_lines, "target distinct len:", num_of_uniq_len, 
                  "target idenctical len:", num_of_same_len)
            print("actual identical:", num_of_same_len, 
                  "percentage:",total_repeated_line_length / total_lines,)
            np.testing.assert_equal(np.sum(distribution), total_bytes)
            return distribution
    
    def generate_text_with_prob(self, identical_word_prob: int, line_distribution: list[int]) -> list[str]: 
        total_words = 0 
        white_space = defaultdict(list) 
        used_word = defaultdict(int)
        word_len = defaultdict(int)
        word_to_use = defaultdict(list)

        # Determine randomly where whitespace should be placed and count words per sentence. 
        for idx, line_num in enumerate(line_distribution): 
            line_num_without_newline = line_num - 1 
            if line_num_without_newline == 1: 
                white_space[idx] = [0] # White-space + new line line
            elif line_num_without_newline > 1: 
                number_of_ws = random.randint(1, round(line_num_without_newline / 2))
                potential_placements = [num for num in range(0, line_num_without_newline)]
                placements = sorted(random.sample(potential_placements, number_of_ws))
                
                # Populate dict of word length to number of words with this length for current line 
                i = 0
                while i in range(line_num_without_newline):  
                    curr_word_len = 0 
                    while i not in placements and i in range(line_num_without_newline): 
                        curr_word_len += 1
                        i += 1 
                    if curr_word_len > 0: 
                        word_len[curr_word_len] += 1
                        total_words += 1
                    i += 1 
                    
                white_space[idx] += placements
            else: 
                white_space[idx] = [] # New line only 
        
        # Generate random words (with repeat when needed) mapping to word lengths.
        repeated_word = ceil(identical_word_prob * total_words)
        print("target identical words: ", repeated_word, "total words", total_words,)
        for l, amt in word_len.items():
            if amt == 1: 
                word_to_use[l].append(self.get_random_word(l))
                continue
            
            if amt > 1 and repeated_word > 0:
                word = self.get_random_word(l)
                if repeated_word - amt < 0: 
                    word_to_use[l] = [word] * repeated_word
                    repeated_word -= amt
                else: 
                    word_to_use[l] = [word] * amt
                    repeated_word -= amt
                    continue
             
            for _ in range(amt): 
                word = self.get_random_word(l)
                trial = 0
                while word in word_to_use[l] and trial < 20:
                    word = self.get_random_word(l)
                    trial += 1 
                word_to_use[l].append(word)
                    
        
        # Generate text using word dict. 
        text = [0] * len(line_distribution)    
        idx = 0 
        for idx, ws_array in white_space.items(): 
            if len(ws_array) == 0: 
                str = '\n'
            else: 
                str = ""
                i = 0 
                while True: 
                    curr_word_len = 0 
                    while i not in ws_array and i in range(line_distribution[idx] - 1): 
                        curr_word_len += 1
                        i += 1 
                    if curr_word_len > 0:
                        word = word_to_use[curr_word_len][0] 
                        word_to_use[curr_word_len] = word_to_use[curr_word_len][1:]
                        used_word[word] += 1 
                    else: 
                        word = ""
                    str += word
                    if i in range(line_distribution[idx] - 1):   
                        str += " "
                        i += 1 
                    else: 
                        break
                str += '\n'
            
            text[idx] = str
            np.testing.assert_equal(len(str), line_distribution[idx])
                    
        total_repeated_word = sum([word for word in used_word.values() if word > 1])
        if total_repeated_word > 0: 
            print("actual identical:", total_repeated_word, "percentage:", total_repeated_word / total_words)
        return text
    
    # Helper functions
    def write_text_to_file(self, text: list[str]):
         with open(self.write_to, "w") as rand_file:  
            for line in text: 
                rand_file.write(line)  
        
    def shuffle_text(self, text: list[int]) -> bool: 
        random.shuffle(text)
        return True
    
    def get_random_word(self, word_len: int) -> str: 
        word = ''.join(random.choices(self.char_pool, k=word_len))
        return word
        

if __name__ == "__main__":
    total_bytes = 2000
    total_lines = 20
    i_line_len_prob = 0.2
    i_word_prob = 0.4
    rand_generator = RandomGeneratorProb("rand.txt", total_bytes, total_lines, i_word_prob, i_line_len_prob) 
    rand_generator.generate()
    
    