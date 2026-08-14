"""
该程序用于研究一维棋盘上的博弈。
记号
    长为l的盘面用形如"[ooo]"的，首尾为中括号的长为(l+2)的字符串表示。环形棋盘改用圆括号。
    "o", "x"分别表示一般的棋子和空位o
    如果棋盘允许拆分（便于堆博弈转化为一维棋盘博弈），则" ", "|"分别表示两位置间相连，拆分。
"""
import pygame
import sys
import time
import numpy.random
from FSA import nfa

# from Py_functions import *
from ACG import *

OUTPUT_PATH = "result\\result.txt"
"""输出txt文件的地址"""

KEY_OUTPUT_PATH = None
"""关键信息的输出地址"""

PRINT_EXAMPLES = True
"""打印出着子的例子"""

OUTCOME = False

LONG_ONLY = True

WEAK_SOLUTION = True
"""只考虑弱可达的局面"""

PARTIZAN_OUTCOME_DICT = {0: "P", 1: "N", (0, 0): "P", (1, 1): "N", (1, 0): "L", (0, 1): "R"}

UNSOLVED_INDEXES = [(6, 5), (7, 5), (7, 6), (7, 7)]
"""未解决的kotzig游戏的编码"""


def mex(sg_list):
    """mex函数"""

    if OUTCOME:
        return 1 if any(sg == 0 for sg in sg_list) else 0
    else:
        now_mex = 0
        while now_mex in sg_list:
            now_mex += 1
        return now_mex


def sg_str(sg):
    if OUTCOME:
        return PARTIZAN_OUTCOME_DICT[sg]
    else:
        if type(sg) is tuple:
            return f"{sg[0]}:{sg[1]}"
        else:
            return f"{sg}"


def write(code, cover=False, key=False, output_path=None, key_output_path=None, end="\n"):
    """打印的同时写入输出文件"""

    code = str(code)

    print(code, end=end)

    if not output_path:
        output_path = OUTPUT_PATH

    if output_path:
        with open(output_path, "w" if cover else "a") as file:
            file.write(code + end)
    if key:

        if key_output_path is None:
            key_output_path = KEY_OUTPUT_PATH

        if key_output_path:
            with open(key_output_path, "w" if cover else "a") as key_file:
                key_file.write(code + end)


class kotzig_game:
    """Kotzig博弈"""

    def __init__(self, S: list[int] | dict[str, list[int]], terminal_sg=0):

        self.charas = ["x", "o"]
        """字（棋子和空位）的列表。"""

        self.S = S
        """步长。"""

        self.recorded_sg = {}
        """记录的SG值"""

        self.terminal_sg = terminal_sg
        """终局的SG值"""

        self.partizan = (type(self.S) is dict)
        """无偏性"""

        self.tags = ["L", "R"] if self.partizan else ["M"]

        if self.partizan:
            self.S["L"].sort()
            self.S["R"].sort()
            self.s_max = max(self.S["L"][-1], self.S["R"][-1])
        else:
            self.S.sort()
            self.s_max = self.S[-1]

    def write_describe(self, key=False):
        """打印描述"""
        if self.partizan:
            game_name = f"Partizan Kotzig game, S={deblank(self.S["L"])}:{deblank(self.S["R"])}"
        else:
            game_name = f"Kotzig game, S={deblank(self.S)}"
        if self.terminal_sg == 1:
            game_name += ", misere"
        elif self.terminal_sg > 1:
            game_name += f", terminal SG={self.terminal_sg}"
        write(f"Game: {game_name}", key=key)

    def write_sg_table(self, key=False):
        """打印SG表"""

        if OUTCOME:
            if game.partizan:
                write(f"OC: {" ".join(len_str(i, 2, "r") for i in range(26))} ...", key=key)
                sg_list_L = [game.get_sg("L" + i * "o") for i in range(26)]
                sg_list_R = [game.get_sg("R" + i * "o") for i in range(26)]
                write(f"    {",".join(len_str(sg_str((sg_list_L[i], sg_list_R[i])), 2, "r")
                                      for i in range(26))} ...",
                      key=key)
                write(f"    Period: {deblank(detect_period(sg_list_L))}:{deblank(detect_period(sg_list_R))}", key=key)
            else:
                write(f"OC: {" ".join(len_str(i, 2, "r") for i in range(26))} ...", key=key)
                sg_list = [game.get_sg("M" + i * "o") for i in range(26)]
                write(f"    {",".join(len_str(sg_str(sg_list[i]), 2, "r") for i in range(26))} ...",
                      key=key)
                write(f"    Period: {deblank(detect_period(sg_list))}", key=key)
        else:
            if game.partizan:
                write(f"SG: {" ".join(len_str(i, 4, "r") for i in range(26))} ...", key=key)
                sg_list_L = [game.get_sg("L" + i * "o") for i in range(26)]
                sg_list_R = [game.get_sg("R" + i * "o") for i in range(26)]
                write(f"    {",".join(len_str(sg_str((sg_list_L[i], sg_list_R[i])), 4, "r")
                                      for i in range(26))} ...",
                      key=key)
                write(f"    Period: {deblank(detect_period(sg_list_L))}:{deblank(detect_period(sg_list_R))}", key=key)
            else:
                write(f"SG: {" ".join(len_str(i, 2, "r") for i in range(26))} ...", key=key)
                sg_list = [game.get_sg("M" + i * "o") for i in range(26)]
                write(f"    {",".join(len_str(sg_str(sg_list[i]), 2, "r") for i in range(26))} ...",
                      key=key)
                write(f"    Period: {deblank(detect_period(sg_list))}", key=key)

    @staticmethod
    def enum_games(max_s=4, undegen=False, solved=None):
        """穷举给定范围内的游戏"""

        for i_L in range(1, 2 ** max_s):
            for i_R in range(1, i_L + 1):

                # 不满足对是否已解决的要求
                if (solved is not None) and ((i_L, i_R) not in UNSOLVED_INDEXES) != solved:
                    continue

                S_L = [s for s in range(max_s + 1) if i_L // (2 ** (s - 1)) % 2 == 1]
                S_R = [s for s in range(max_s + 1) if i_R // (2 ** (s - 1)) % 2 == 1]

                # 不满足对非退化性的要求
                if undegen and (len(S_L) <= 1 or len(S_R) <= 1):
                    continue

                if len(S_L) < 1 or len(S_R) < 1:
                    continue

                if gcd(S_L + S_R) > 1:
                    continue

                for terminal_sg in [0, 1]:
                    if S_L == S_R:
                        yield kotzig_game(S=S_L, terminal_sg=terminal_sg)
                    else:
                        yield kotzig_game(S={"L": S_L, "R": S_R}, terminal_sg=terminal_sg)

    def switch_tag(self, tag):

        if tag == "L":
            return "R"
        elif tag == "R":
            return "L"
        else:
            return tag

    def get_next_words(self, word, return_s=False):
        """以生成器形式给出一个盘面所有接下来的盘面"""

        if len(word) <= 1:
            return

        for s in (self.S[word[:1]] if self.partizan else self.S):

            next_i = s % len(word)
            if next_i == 0:
                continue

            if word[next_i] == "o":
                next_word = f"{self.switch_tag(word[:1])}{word[next_i + 1:]}x{word[1:next_i]}"

                yield (next_word, s) if return_s else next_word

    def natural_reduce(self, word):
        """词的自然归约"""

        # 将不可达的空位都换成障碍
        if not self.partizan:
            for i in range(self.s_max + 1, len(word)):

                # 该位置是空位
                if word[i] == "o":

                    # 该位置不可达，换成障碍
                    if all(word[i - s] == "x" for s in self.S):
                        word = word[:i] + "x" + word[i + 1:]
        else:
            for i in range(self.s_max + 1, len(word)):

                # 该位置是空位
                if word[i] == "o":

                    # 该位置不可达，换成障碍
                    if all(word[i - s] == "x" for tag in "LR" for s in self.S[tag]):
                        word = word[:i] + "x" + word[i + 1:]

        full_barrier = self.s_max * "x"

        # 截断完全障碍后的词
        if full_barrier in word:
            i = word.index(full_barrier)
            word = f"{word[:i]}{full_barrier}"

        return word

    def get_sg(self, word: str | tuple):
        """求sg值"""

        # if len(word) <= self.s_max:
        #     return self.terminal_sg

        if WEAK_SOLUTION and any(len(o_serie) >= self.s_max for o_serie in word.split("x")[1:]):
            return self.terminal_sg

        # 自然归约
        word = self.natural_reduce(word)

        # 已记录SG值
        sg = self.recorded_sg.get(word, None)

        # 不在已记录范围，则计算后进行记录
        if sg is None:

            next_sg_set = {self.get_sg(next_word) for next_word in self.get_next_words(word)}

            if next_sg_set:
                sg = mex(next_sg_set)
            else:
                sg = self.terminal_sg

            self.recorded_sg[word] = sg

        return sg

    def word_str(self, word, show_sg=True):
        """用于打印的盘面字符串"""

        return f"{word}{f"_{self.get_sg(word)}" if show_sg else ""}"

    def enum_test_suffix(self, max_size):
        """枚举用于测试的后缀"""

        for suffix in enum_words(self.charas, range(max_size + 1)):

            # # 要求后缀为(xo^S)*形式
            if WEAK_SOLUTION and any(len(o_serie) >= self.s_max for o_serie in suffix.split("x")[1:]):
                # print(f"  {suffix} not reachable")
                continue

            # 要求后缀是自然归约的
            if self.natural_reduce(suffix) != suffix:
                # print(f"  {suffix} not reduced (->{self.natural_reduce(suffix)})")
                continue

            yield suffix

    def prefix_cong(self, prefix1, prefix2, test_suffixes):
        """用给定的测试后缀集测试两个前缀是否同余"""

        # if len(prefix1.split("X")[-1])!=len(prefix2.split("X")[-1]):
        #     return False

        for suffix in test_suffixes:
            word1 = prefix1 + suffix
            word2 = prefix2 + suffix

            if self.get_sg(word1) != self.get_sg(word2):
                return False

        return True

    def get_sg_nfa(self, test_suffixes, max_state_num=1000, max_record_num=5000000):
        """根据归约给出确定具有某个SG值或OC值的局面的nfa"""

        if OUTCOME:

            if self.partizan:
                P_nfa = nfa(trans_map={("", "L"): {"L"}, ("", "R"): {"R"}, },
                            charas=self.charas + ["L", "R"],
                            states=["", "L", "R"],
                            init_states={""},
                            final_states=set(),
                            name=f"P{"^-" if self.terminal_sg > 0 else ""}"
                                 f"({deblank(self.S["L"])}:{deblank(self.S["R"])})")
                queue = ["Lx", "Lo", "Rx", "Ro"]
            else:
                P_nfa = nfa(trans_map={("", "M"): {"M"}, },
                            charas=self.charas + ["M"],
                            states=["", "M"],
                            init_states={""},
                            final_states=set(),
                            name=f"P{"^-" if self.terminal_sg > 0 else ""}({deblank(self.S)})")
                queue = ["Mx", "Mo"]
            N_nfa_final_states = set()

            while len(queue) > 0:

                # 从队列中弹出新的状态
                now_state = queue.pop(0)

                reduced = False

                # 检查该前缀是否可归约成已记录的状态
                if (not LONG_ONLY) or len(now_state) > self.s_max:
                    # if (not LONG_ONLY) or len(now_state) >= self.s_max:
                    for old_state in P_nfa.states:

                        if old_state not in P_nfa.final_states and old_state not in N_nfa_final_states:
                            continue

                        if self.prefix_cong(old_state, now_state, test_suffixes):
                            P_nfa.add_trans((now_state[:-1], now_state[-1]), old_state)
                            # print(f"    New reductive trans added: {now_state[:-1]}·{now_state[-1]}->{old_state}")
                            reduced = True
                            break

                if reduced:
                    continue

                # 该前缀是一个未被记录的新状态，或者过短的状态，将其记入状态集；如果sg值符合则为终止状态
                P_nfa.states.append(now_state)
                if (not LONG_ONLY) or len(now_state) > self.s_max:
                    # if (not LONG_ONLY) or (len(now_state) >= self.s_max):
                    sg = self.get_sg(now_state)
                    if sg == 0:
                        P_nfa.final_states.add(now_state)
                        # print(f"    New {"P" if is_final else "N"}-state added: {now_state}")
                    elif sg == 1:
                        N_nfa_final_states.add(now_state)

                # 平凡的转移
                P_nfa.add_trans((now_state[:-1], now_state[-1]), now_state)

                if len(P_nfa.states) > max_state_num:
                    write(f"  \033[31mState number overflow (>{max_state_num})!\033[0m", key=True)
                    # print(f"    remained states: {", ".join(queue[:100])},...")
                    return None, None

                # 在前缀后加o和x继续等待归约
                for chara in self.charas:
                    new_state = now_state + chara

                    # # 要求前缀除第一段外空格长度均小于最大步长
                    # if WEAK_SOLUTION and any(len(o_serie) >= self.s_max for o_serie in new_state.split("x")[1:]):
                    #     continue

                    queue.append(new_state)
                    # else:
                    #     print(f"{new_state} illegal")

                # 记录的SG数溢出，停止搜索
                if len(self.recorded_sg) > max_record_num:
                    write(f"  \033[31mRecorded SG overflow (number >{max_record_num})!\033[0m", key=True)
                    # print(f"    states: {", ".join(queue[:100])},...")
                    return None, None
                # else:
                #     print(f"  ({len(queue)} states left: {", ".join(queue[:10])},...)")

            N_nfa = P_nfa.copy()
            N_nfa.final_states = N_nfa_final_states
            if self.partizan:
                N_nfa.name = f"N{"^-" if self.terminal_sg > 0 else ""}({deblank(self.S["L"])}:{deblank(self.S["R"])})"
            else:
                N_nfa.name = f"N{"^-" if self.terminal_sg > 0 else ""}({deblank(self.S)})"

            # 如果是弱解模式，得到的DFA需要删去其中包含的非弱可达局面
            if WEAK_SOLUTION:

                # 弱可达的局面
                weak_reachable = (nfa.words_acceptor(self.tags)
                                  * (nfa.words_acceptor(["o"]) * "*")
                                  * (nfa.words_acceptor(["x" + s * "o" for s in range(self.s_max)]) * "*"))
                weak_reachable.name = "W"

                # print("-"*50)
                # print(weak_reachable)
                # print("-"*50)
                # print(P_nfa)
                # print("-"*50)
                # print(N_nfa)

                P_nfa = P_nfa & weak_reachable
                N_nfa = N_nfa & weak_reachable

                if self.partizan:
                    P_nfa.name = (f"P_qr{"^-" if self.terminal_sg > 0 else ""}"
                                  f"({deblank(self.S["L"])}:{deblank(self.S["R"])})")
                    N_nfa.name = (f"N_qr{"^-" if self.terminal_sg > 0 else ""}"
                                  f"({deblank(self.S["L"])}:{deblank(self.S["R"])})")
                else:
                    P_nfa.name = f"P_qr{"^-" if self.terminal_sg > 0 else ""}({deblank(self.S)})"
                    N_nfa.name = f"N_qr{"^-" if self.terminal_sg > 0 else ""}({deblank(self.S)})"

            return P_nfa, N_nfa

        else:

            if self.partizan:
                P_nfa = nfa(trans_map={("", "L"): {"L"}, ("", "R"): {"R"}, },
                            charas=self.charas + ["L", "R"],
                            states=["", "L", "R"],
                            init_states={""},
                            final_states=set(),
                            name=f"P{"^-" if self.terminal_sg > 0 else ""}_{deblank(self.S["L"])}:{deblank(self.S["R"])}")
                queue = ["Lx", "Lo", "Rx", "Ro"]
                max_sg = max(len(self.S["L"]), len(self.S["R"]))
            else:
                P_nfa = nfa(trans_map={("", "M"): {"M"}, },
                            charas=self.charas + ["M"],
                            states=["", "M"],
                            init_states={""},
                            final_states=set(),
                            name=f"P{"^-" if self.terminal_sg > 0 else ""}_{deblank(self.S)}")
                queue = ["Mx", "Mo"]
                max_sg = len(self.S)

            final_states_list = [set() for _ in range(max_sg + 1)]
            # print(f"final_states_list={final_states_list}")

            while len(queue) > 0:

                # 从队列中弹出新的状态
                now_state = queue.pop(0)

                reduced = False

                # 检查该前缀是否可归约成已记录的状态
                if (not LONG_ONLY) or len(now_state) > self.s_max:
                    # if (not LONG_ONLY) or len(now_state) >= self.s_max:
                    for old_state in P_nfa.states:

                        if (old_state not in P_nfa.final_states
                                and all(old_state not in final_states for final_states in final_states_list)):
                            continue

                        if self.prefix_cong(old_state, now_state, test_suffixes):
                            P_nfa.add_trans((now_state[:-1], now_state[-1]), old_state)
                            # print(f"    New reductive trans added: {now_state[:-1]}·{now_state[-1]}->{old_state}")
                            reduced = True
                            break

                if reduced:
                    continue

                # 该前缀是一个未被记录的新状态，或者过短的状态，将其记入状态集；如果sg值符合则为终止状态
                P_nfa.states.append(now_state)
                if (not LONG_ONLY) or len(now_state) > self.s_max:
                    # if (not LONG_ONLY) or (len(now_state) >= self.s_max):
                    sg = self.get_sg(now_state)
                    if sg == 0:
                        P_nfa.final_states.add(now_state)
                        # print(f"    New {"P" if is_final else "N"}-state added: {now_state}")

                    final_states_list[sg].add(now_state)

                # 平凡的转移
                P_nfa.add_trans((now_state[:-1], now_state[-1]), now_state)

                if len(P_nfa.states) > max_state_num:
                    write(f"  \033[31mState number overflow (>{max_state_num})!\033[0m", key=True)
                    # print(f"    remained states: {", ".join(queue[:100])},...")
                    return None, None

                # 在前缀后加o和x继续等待归约
                for chara in self.charas:
                    new_state = now_state + chara

                    # 要求前缀除第一段外空格长度均小于最大步长
                    if WEAK_SOLUTION and any(len(o_serie) >= self.s_max for o_serie in new_state.split("x")[1:]):
                        continue

                    queue.append(new_state)
                    # else:
                    #     print(f"{new_state} illegal")

                # 记录的SG数溢出，停止搜索
                if len(self.recorded_sg) > max_record_num:
                    write(f"  \033[31mRecorded SG overflow (number >{max_record_num})!\033[0m", key=True)
                    # print(f"    states: {", ".join(queue[:100])},...")
                    return None, None

            # 如果是弱解模式，得到的DFA需要删去其中包含的非弱可达局面
            if WEAK_SOLUTION:

                # 弱可达的局面
                weak_reachable = (nfa.words_acceptor(self.tags)
                                  * (nfa.words_acceptor(["o"]) * "*")
                                  * (nfa.words_acceptor(["x" + s * "o" for s in range(self.s_max)]) * "*"))
                weak_reachable.name = "W"
                #
                # print(f"sg=0, final states={P_nfa.final_states}")
                # P_nfa = P_nfa & weak_reachable
                # print(f"sg=0, new final states={P_nfa.final_states}")

                new_final_states_list = []
                for sg, final_states in enumerate(final_states_list):

                    if sg == 0:
                        new_final_states_list.append(P_nfa.final_states)

                    else:

                        N_nfa = P_nfa.copy()
                        N_nfa.final_states = final_states.copy()
                        #
                        # print(f"sg={sg}, N_nfa=\n{N_nfa}")

                        new_N_nfa = N_nfa & weak_reachable
                        #
                        # print(f"sg={sg}, new N_nfa=\n{N_nfa}")

                        new_final_states_list.append(new_N_nfa.final_states)
                final_states_list = new_final_states_list

                # print(f"New final states={new_final_states_list}")

                if self.partizan:
                    P_nfa.name = (f"P_qr{"^-" if self.terminal_sg > 0 else ""}"
                                  f"({deblank(self.S["L"])}:{deblank(self.S["R"])})")
                else:
                    P_nfa.name = f"P_qr{"^-" if self.terminal_sg > 0 else ""}({deblank(self.S)})"

            return P_nfa, final_states_list

    def get_next_nfa(self, A: nfa):

        nfa_list = []

        if self.partizan:
            for s in self.S["L"]:
                for prefix in enum_words(self.charas, s - 1):
                    new_A = (nfa.words_acceptor("R")
                             * A.remove_prefix("L" + prefix + "o")
                             * nfa.words_acceptor("x" + prefix))
                    nfa_list.append(new_A)
            for s in self.S["R"]:
                for prefix in enum_words(self.charas, s - 1):
                    new_A = (nfa.words_acceptor("L") * A.remove_prefix("R" + prefix + "o")
                             * nfa.words_acceptor("x" + prefix))
                    nfa_list.append(new_A)

        else:

            for s in self.S:
                for prefix in enum_words(self.charas, s - 1):
                    new_A = (nfa.words_acceptor("M")
                             * A.remove_prefix("M" + prefix + "o")
                             * nfa.words_acceptor("x" + prefix))
                    nfa_list.append(new_A)

        next_nfa = nfa_list[0]
        for new_A in nfa_list[1:]:
            next_nfa = next_nfa | new_A

        return next_nfa

    def get_prev_nfa(self, A: nfa):

        nfa_list = []

        if self.partizan:
            for s in self.S["L"]:
                for suffix in enum_words(self.charas, s - 1):
                    new_A = nfa.words_acceptor("L" + suffix + "o") * A.remove_suffix("x" + suffix).remove_prefix("R")
                    nfa_list.append(new_A)

            for s in self.S["R"]:
                for suffix in enum_words(self.charas, s - 1):
                    new_A = nfa.words_acceptor("R" + suffix + "o") * A.remove_suffix("x" + suffix).remove_prefix("L")
                    nfa_list.append(new_A)


        else:
            for s in self.S:
                for suffix in enum_words(self.charas, s - 1):
                    new_A = nfa.words_acceptor("M" + suffix + "o") * A.remove_suffix("x" + suffix).remove_prefix("M")
                    nfa_list.append(new_A)

        prev_nfa = nfa_list[0]
        for new_A in nfa_list[1:]:
            prev_nfa = prev_nfa | new_A

        return prev_nfa

    def get_terminals_nfa(self):
        """给出所有终局的nfa"""

        if self.partizan:
            prefixes = (["L" + prefix for prefix in enum_words(self.charas, self.s_max) if
                         all(prefix[s - 1] == "x" for s in self.S["L"])]
                        + ["R" + prefix for prefix in enum_words(self.charas, self.s_max) if
                           all(prefix[s - 1] == "x" for s in self.S["R"])])
        else:
            prefixes = [prefix for prefix in enum_words(self.charas, self.s_max) if
                        all(prefix[s - 1] == "x" for s in self.S)]

        term_nfa = nfa.words_acceptor(prefixes) * (nfa.words_acceptor(self.charas) * "*")

        return term_nfa

    def check_P_nfa(self, P_nfa, N_nfa=None, test_size=20):
        """初步检查得到的nfa是否正确"""

        correct = True
        print(f"Excluded words:")

        for word in enum_words(self.charas, range(self.s_max, test_size + 1)):

            sg = self.get_sg(word)
            if P_nfa(word) and sg != 0:
                print(f"  o({word})={sg} ->0 !")
                correct = False
            elif N_nfa is not None and N_nfa(word) and sg == 0:
                print(f"  o({word})={sg} ->1 !")
                correct = False

        if correct:
            print(f"NFA correct!")

    def prove_P_nfa(self, P_nfa, N_nfa):
        """证明找到的P-nfa和N-nfa是正确的，返回游戏类型"""

        if not LONG_ONLY:
            P_nfa = (nfa.words_acceptor([tag for tag in self.tags])
                     * (nfa.words_acceptor(list(enum_words(["o", "x"], self.s_max))))
                     * (nfa.words_acceptor(["o", "x"]) * "+")) & P_nfa
            N_nfa = (nfa.words_acceptor([tag for tag in self.tags])
                     * (nfa.words_acceptor(list(enum_words(["o", "x"], self.s_max))))
                     * (nfa.words_acceptor(["o", "x"]) * "+")) & N_nfa

        write("-" * 50, key=True)

        try:
            next_P_nfa = self.get_next_nfa(P_nfa)
            next_P_nfa.name = f"next({P_nfa.name})"

            # print("-"*50)
            # print(next_P_nfa)

            prev_P_nfa = self.get_prev_nfa(P_nfa)
            prev_P_nfa.name = f"prev({P_nfa.name})"

            # print("-" * 50)
            # print(prev_P_nfa)

            term_nfa = self.get_terminals_nfa()

        # 自动机状态数溢出
        except OverflowError:
            write(f"\033[31mPrev/Next-DFA state number overflowed (>{50000})!\033[0m ", key=True)
            return "X"

        write(f"Final/total state nums:", key=True)
        write(f"  P: {len(P_nfa.final_states)}/{len(P_nfa.states)}", key=True)
        write(f"  N: {len(N_nfa.final_states)}/{len(N_nfa.states)}", key=True)
        write(f"  prev(P): {len(prev_P_nfa.final_states)}/{len(prev_P_nfa.states)}", key=True)
        write(f"  next(P): {len(next_P_nfa.final_states)}/{len(next_P_nfa.states)}", key=True)

        # term_nfa = self.get_terminals_nfa()

        # 需要满足的三个条件
        conds = {"T": None, "0": None, "1": None}
        cond_texts = {"T": f"T <= {"P" if game.terminal_sg == 0 else "N"}",
                      "0": "next(P) <= N",
                      "1": f"{"N" if game.terminal_sg == 0 else "(N \\ T)"} <= prev(P)"}

        write("-" * 50, key=True)
        write(f"Conditions:", key=True)

        excluded_words = []

        for cond_code in "T01":
            # for cond_code in "0":

            cond = None
            try:
                # 条件T：终局一定是P局面（misere规则则一定是N局面）
                if cond_code == "T":
                    nfa1 = term_nfa
                    nfa2 = P_nfa if game.terminal_sg == 0 else N_nfa
                    # cond = (term_nfa <= P_nfa) if game.terminal_sg == 0 else (term_nfa <= N_nfa)
                # if not cond:
                #     excluded_words=[word for word in range(20)]

                # 条件0： P局面可达的一定是N局面，next(P) <= N
                elif cond_code == "0":
                    nfa1 = next_P_nfa
                    nfa2 = N_nfa
                    # cond = next_P_nfa <= N_nfa

                else:
                    nfa1 = N_nfa if (game.terminal_sg == 0) else (N_nfa - term_nfa)
                    nfa2 = prev_P_nfa
                    # cond = (N_nfa if game.terminal_sg == 0 else (N_nfa - term_nfa)) <= prev_P_nfa

                cond = nfa1 <= nfa2

                if not cond:
                    excluded_words = [tag + word for tag in self.tags
                                      for word in enum_words(self.charas, range(TEST_SIZE + 5 + 1))
                                      if nfa1(tag + word) and not nfa2(tag + word)]

            except OverflowError:
                cond = None

            conds[cond_code] = cond

            write(f"  {cond_texts[cond_code]}: "
                  f"{"\033[32mTrue\033[0m" if cond else "\033[31mFalse\033[0m"}", key=True)

            if not cond:
                break

        if not all(conds.values()):
            write("\033[31mFailed to prove!\033[0m "
                  f"({len(N_nfa.states)} states)", key=True)
            write(f"  Excluded (len<={TEST_SIZE + 5}): {", ".join(excluded_words)}")
            return "x"

        else:
            # 各种状态的计数
            if self.partizan:
                class_nums = (len(P_nfa.final_states), len(N_nfa.final_states))
                write("\033[32mSucceed to prove!\033[0m "
                      f"(P, N-class num={",".join(str(num) for num in class_nums)} (sum={sum(class_nums)}), "
                      f"state num={len(N_nfa.states)})", key=True)
            else:
                class_nums = (len(P_nfa.final_states), len(N_nfa.final_states))
                write("\033[32mSucceed to prove!\033[0m "
                      f"(P,N-class num={",".join(str(num) for num in class_nums)} (sum={sum(class_nums)}), "
                      f"state num={len(N_nfa.states)})", key=True)
            return "V"


result_index = 0

if WEAK_SOLUTION:
    OUTPUT_PATH = f"result\\kotzig\\kotzig_weak_solutions.txt"
    """输出txt文件的地址"""

    KEY_OUTPUT_PATH = f"result\\kotzig\\kotzig_weak_solutions_key.txt"
    """输出的关键信息的txt文件的地址"""

else:
    OUTPUT_PATH = f"result\\kotzig\\kotzig_solutions.txt"

    KEY_OUTPUT_PATH = f"result\\kotzig\\kotzig_solutions_key.txt"
    """输出的关键信息的txt文件的地址"""

OUTPUT_PATH = f"result\\kotzig\\kotzig_pseper.txt"

KEY_OUTPUT_PATH = f"result\\kotzig\\kotzig_pseper_key.txt"
"""输出的关键信息的txt文件的地址"""

TEST_SIZE = 12

MAX_RECORD_NUM = 20000000
MAX_STATE_NUM = 5000

write(f"Date: 2026/7/29", key=True, cover=True)
write(f"Parameters:\n"
      f"  MAX_STATE_NUM={MAX_STATE_NUM};\n"
      f"  MAX_RECORD_NUM={MAX_RECORD_NUM};\n"
      f"  TEST_SIZE={TEST_SIZE};\n"
      f"  WEAK_SOLUTION={WEAK_SOLUTION};", key=True)

for game in kotzig_game.enum_games(max_s=3, undegen=True):

    # if game.partizan or game.S not in [[2, 3, 4, 6], [1, 2, 3, 4, 6], [1, 2, 3, 5, 6], [1, 2, 3, 4, 7]]:
    #     continue

    if not OUTCOME and (game.partizan or game.terminal_sg > 0):
        continue

    write("=" * 50, key=True)
    game.write_describe(key=True)

    test_size = TEST_SIZE
    test_suffixes = sorted(game.enum_test_suffix(test_size))
    write(f"  ({len(test_suffixes)} test suffixes for size<={test_size})", key=True)

    if OUTCOME:

        P_nfa, N_nfa = game.get_sg_nfa(test_suffixes, MAX_STATE_NUM, MAX_RECORD_NUM)

        if P_nfa is None:
            write(f"P-NFA not found!", key=True)
            continue

        P_nfa: nfa
        N_nfa: nfa

        write("-" * 50)
        write(P_nfa.describe())
        write("-" * 50)
        write(N_nfa.describe())

        game.prove_P_nfa(P_nfa, N_nfa)
        # game.check_P_nfa(P_nfa, N_nfa)
        #

        pers = []
        write("-" * 50, key=True)

        game.write_sg_table(key=True)

        for tag in "LR" if game.partizan else "M":
            per = None
            state_list = []
            for n in range(100):
                word = tag + "o" * n

                state = P_nfa.final({""}, word)

                for p, old_state in enumerate(state_list):
                    if old_state == state:
                        per = (p, len(state_list) - p)
                        pers.append(per)

                        state_list.append(state)
                        break

                if per is not None:

                    break
                else:
                    state_list.append(state)

            if per is None:
                pers.append(per)

            # write(f"State list={state_list}")
        write(f"State period: {":".join(deblank(per) for per in pers)}", key=True)

    else:
        P_nfa, final_states_list = game.get_sg_nfa(test_suffixes, MAX_STATE_NUM, MAX_RECORD_NUM)

        if P_nfa is None:
            write(f"P-NFA not found!", key=True)
            continue

        P_nfa: nfa

        write("-" * 50)
        write(P_nfa.describe())

        write("-" * 50)
        write(f"SG final states:")
        for sg in range(len(final_states_list)):
            write(f"    {sg} (size={len(final_states_list[sg])}): {final_states_list[sg]}")

        pers = []
        write("-" * 50, key=True)

        game.write_sg_table(key=True)

        for tag in "LR" if game.partizan else "M":
            per = None
            state_list = []
            for n in range(100):
                word = tag + "o" * n

                state = P_nfa.final({""}, word)

                for p, old_state in enumerate(state_list):
                    if old_state == state:
                        per = (p, len(state_list) - p)
                        pers.append(per)

                        state_list.append(state)
                        break

                if per is not None:

                    break
                else:
                    state_list.append(state)

            if per is None:
                pers.append(per)

            # write(f"State list={state_list}")
        write(f"State period: {":".join(deblank(per) for per in pers)}", key=True)

"""
Normal rule:
{1,2}             & 11,3  & 34 & 0,1,0,1,2,2,0,1,2,1,2,2,1,1,2,1,1,2,1,1,2,1,1,2,1,1,2,1,1,2,1,1,2,1,ooo \\
{1,3}             & 0,6   & 40 & 0,1,0,1,2,1,0,1,0,1,2,1,0,1,0,1,2,1,0,1,0,1,2,1,0,1,0,1,2,1,0,1,0,1,2,1,0,1,0,1,ooo \\
{2,3}             & 11,5  & 40 & 0,0,0,1,0,1,0,0,2,2,0,0,0,2,2,2,0,0,2,2,2,0,0,2,2,2,0,0,2,2,2,0,0,2,2,2,0,0,2,2,ooo \\
{1,2,3}           & 16,4  & 28 & 0,1,0,1,0,1,2,1,3,2,0,1,2,2,0,1,2,3,0,2,2,3,0,2,2,3,0,2,ooo \\
{1,4}             & 25,5  & 43 & 0,1,0,1,0,1,0,1,2,2,2,1,2,1,0,2,1,2,2,2,2,1,0,2,2,2,1,0,2,1,2,1,0,2,1,2,1,0,2,1,2,1,0,ooo \\
{1,2,4}           & ?     & 29 & 0,1,0,1,0,1,0,1,0,3,0,2,0,1,0,1,0,2,0,1,0,1,0,2,0,2,0,3,0,ooo \\
{3,4}             & 23,7  & 43 & 0,0,0,1,2,1,0,1,0,1,1,1,2,2,0,2,1,1,1,2,2,2,0,1,1,1,2,2,2,2,1,1,1,2,2,2,2,1,1,1,2,2,2,ooo \\
{1,3,4}           & ?     & 30 & 0,1,0,1,0,1,0,1,3,3,1,0,1,2,0,1,1,1,0,2,0,1,0,0,2,0,1,2,3,0,ooo \\
{2,3,4}           & ?     & 30 & 0,0,0,1,0,1,0,1,3,1,0,0,2,2,3,1,0,0,3,2,2,3,0,0,1,1,3,1,0,0,ooo \\
{1,2,3,4}         & 9,2   & 26 & 0,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,ooo \\
Misere rule:
{1,2}             & 9,3   & 34 & 1,0,1,0,2,2,0,0,1,0,0,2,0,0,2,0,0,2,0,0,2,0,0,2,0,0,2,0,0,2,0,0,2,0,ooo \\
{1,3}             & 0,6   & 40 & 1,0,1,0,2,2,1,0,1,0,2,2,1,0,1,0,2,2,1,0,1,0,2,2,1,0,1,0,2,2,1,0,1,0,2,2,1,0,1,0,ooo \\
{2,3}             & 8,1   & 40 & 1,1,1,0,1,1,1,2,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,ooo \\
{1,2,3}           & ?     & 28 & 1,0,1,0,1,0,1,0,1,1,2,0,3,1,1,3,2,2,1,3,2,3,3,3,2,2,3,3,ooo \\
{1,4}             & 14,5  & 43 & 1,0,1,0,1,0,0,1,1,1,2,1,1,0,1,2,1,2,1,1,2,1,2,1,1,2,1,2,1,1,2,1,2,1,1,2,1,2,1,1,2,1,2,ooo \\
{1,2,4}           & ?     & 29 & 1,0,1,0,1,0,1,2,1,2,0,0,1,2,1,0,2,2,0,3,0,0,2,1,3,2,2,0,2,ooo \\
{3,4}             & 13,7  & 43 & 1,1,1,0,2,1,1,1,1,0,0,2,1,1,1,2,0,0,2,2,1,1,2,0,0,2,2,1,1,2,0,0,2,2,1,1,2,0,0,2,2,1,1,ooo \\
{1,3,4}           & ?     & 30 & 1,0,1,0,1,2,1,0,2,0,1,0,2,2,0,1,2,1,1,1,1,0,1,0,1,1,3,1,1,3,ooo \\
{2,3,4}           & ?     & 30 & 1,1,1,0,1,0,1,0,1,0,1,0,1,3,2,0,3,0,1,3,2,0,1,1,0,3,2,3,1,3,ooo \\
{1,2,3,4}         & ?     & 26 & 1,0,1,0,1,0,1,0,2,0,1,0,2,0,1,0,1,4,2,3,1,0,1,3,1,0,ooo \\

"""

"""
6,3  6,1  
3,6  3,12
4,5  3,5
"""
