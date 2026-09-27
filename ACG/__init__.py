"""
自动机（Automata），组合学（Combinatorics）与博弈论（Games）相关的基础的函数与类
"""

from PIL import Image, ImageDraw, ImageFont
import math

"""内部的字符串处理"""


def deblank(word):
    """去掉字符串的空格，用来打印字符。"""
    return "".join(str(word).split(" "))


def debucket(word, buckets=("([{", ")]}"), remove_comma=True):
    """去掉字符串的括号"""

    bucs, kets = buckets

    word=str(word)

    while word[:1] in bucs and word[-1:] in kets:
        word = word[1:-1]
        if remove_comma and word[-1:] == ",":
            word = word[:-1]

    return word

def len_str(word, length=5, align="l", blank=" "):
    """具有固定长度和颜色的字符串"""

    word = str(word)

    if len(word) < length:
        if "r" in align:  # 右对齐
            word = blank * (length - len(word)) + word
        elif "c" in align:  # 中对齐
            left_blank_num = (length - len(word)) // 2
            right_blank_num = length - len(word) - left_blank_num
            word = blank * left_blank_num + word + blank * right_blank_num
        else:  # 左对齐（默认）
            word += blank * (length - len(word))

    return word


def array_str(array: list, max_width=None, lengths=None, aligns=None, seper=", ", buckets=("", "")):
    """序列的字符"""
    text = buckets[0]

    if max_width is not None and len(array) > max_width:
        array = array[:max_width]
        array.append("...")

    if lengths is None:
        text += seper.join(str(word) for word in array)
    elif type(lengths) is int:
        text += seper.join(len_str(word, lengths, aligns) for word in array)
    elif type(lengths) is list:
        text += seper.join(len_str(word, lengths[i if i < len(lengths) else lengths[-1]],
                                   aligns if type(aligns) is not list else aligns[
                                       i if i < len(lengths) else aligns[-1]])
                           for i, word in enumerate(array))

    text += buckets[1]

    return text


def table_str(table: list[list], max_width=None, max_height=None, lengths=None, aligns=None, seper=", ",
              buckets=("", ""), head_tail=("", ""), fixed_width=False):
    """表格的字符"""

    if max_width is None:
        max_width = max(len(line) for line in table)

    # 分隔符是" & "时默认为latex格式
    if seper == " & " and buckets is None and head_tail is None:

        if aligns is None:
            aligns = ["l" for _ in range(max_width)]
        elif type(aligns) is str:
            aligns = [aligns for _ in range(max_width)]

        buckets = ("    ", " \\\\")
        head_tail = ("\\begin{tabular}{" + "|".join(aligns) + "}", "\\end{tabular}")
        fixed_width = True

    # 宽度固定则在不够宽的行后面添加空格
    if fixed_width:
        table = [line + ["" for _ in range(max_width - len(line))] for line in table]

    # 超出高度则截断并加省略号
    if len(table) > max_height:
        table = table[:max_width]
        table.append(["..." for _ in range(max_width)])

    # 超出宽度则截断并加省略号
    if any(len(line) > max_width for line in table):
        for i in range(len(table)):
            if len(table[i]) > max_width:
                table[i] = table[i][:max_width]
                table[i].append("...")
            else:
                table[i].append("")

    text = head_tail[0]
    text += "\n".join(array_str(line, max_width, lengths, aligns, seper, buckets) for line in table)
    text += head_tail[1]

    return text


"""基础的数论函数"""


def gcd(a, b=None):
    """最大公因数"""

    # 两个数的最大公因数，辗转相除法
    if b is not None:

        # 使得a>=b
        if b > a:
            a, b = b, a

        if b == 0:
            return a
        else:
            return gcd(b, a % b)

    # 多个数的最大公因数
    else:
        d = None
        for n in a:
            if d is None:
                d = n
            else:
                d = gcd(d, n)
        return d


def binary_sum(*nums):
    """二进制和函数"""
    s = 0
    for num in nums:
        s ^= num
    return s


def mex(nums):
    """mex函数"""

    now_mex = 0

    if type(nums) is set:
        while now_mex in nums:
            now_mex += 1

    else:

        # 当前的mex和已找到的比起更大的数
        greater_nums = set()

        # 枚举找到的SG值
        for num in nums:

            # 与now_mex相等则重新计算
            if num == now_mex:

                now_mex += 1
                while now_mex in greater_nums:
                    greater_nums.remove(now_mex)
                    now_mex += 1

            # 比now_mex大则加入greater_nums
            elif nums > now_mex:
                greater_nums.add(num)

    return now_mex


def fac(n, m=1):
    """阶乘"""

    if n <= m:
        return 1
    else:
        return n * fac(n - 1, m)

"""词与序列相关的函数"""


def enum_words(charas: list[str | tuple], length: int | list[int] | range,
               buckets: tuple[str, str] = ("", ""),
               max_counts: dict[str | tuple:int] = None):
    """枚举特定字母表和长度的所有词"""

    if type(length) is int:
        buc, ket = buckets

        if (type_buk := type(buc)) is str:
            empty_buc, empty_ket = "", ""
        elif type_buk is tuple:
            empty_buc, empty_ket = (), ()
        else:
            raise TypeError

        if length == 0:
            yield buc + ket
        else:

            for chara in charas:

                # 没有字数限制
                if max_counts is None or chara not in max_counts:
                    for ex_word in enum_words(charas, length - 1, (buc, empty_ket), max_counts):
                        yield ex_word + chara + ket

                # 有字数限制
                else:

                    # 字符数耗尽，无法添加该字符
                    if max_counts[chara] == 0:
                        continue

                    else:
                        next_max_counts = max_counts.copy()
                        next_max_counts[chara] -= 1
                        for ex_word in enum_words(charas, length - 1, (buc, empty_ket), next_max_counts):
                            yield ex_word + chara + ket

    else:
        for l in length:
            for word in enum_words(charas, l, buckets):
                yield word


def enum_int_partitions(summary, length=None, int_range: int | tuple = 1, min_diff=None):
    """枚举具有固定的和的整数序列"""

    if type(summary) is int:

        if type(int_range) is int:
            int_range = (int_range, summary)
        if length is None:
            if int_range[0] > 0:
                length = range(1, summary // int_range[0] + 1)
            else:
                raise ValueError

        if type(length) is int:

            if summary > length * int_range[1]:
                return

            if length == 0 and summary == 0:
                yield ()
            elif length == 1 and (int_range[0] <= summary < int_range[1]):
                yield (summary,)

            else:
                for num in range(int_range[0], int_range[1]):

                    if min_diff is not None:
                        ex_int_range = (int_range[0], min(int_range[1], num - min_diff + 1))
                        # if ex_int_range[1]<ex_int_range[0]:
                        #     continue
                    else:
                        ex_int_range = int_range

                    for ex_serie in enum_int_partitions(summary - num, length - 1, ex_int_range, min_diff):
                        yield ex_serie + (num,)

        else:
            for l in length:
                for serie in enum_int_partitions(summary, l, int_range, min_diff):
                    yield serie
    else:
        for s in summary:
            for serie in enum_int_partitions(s, length, int_range, min_diff):
                yield serie


def enum_rotated(charas):
    """枚举全部的n-轮换"""
    if type(charas) is int:
        charas = [i for i in range(charas)]

    for i in range(len(charas)):
        yield charas
        charas = charas[1:] + charas[0]


def enum_permuted(charas):
    """枚举全部的n-置换"""
    if type(charas) is int:
        charas = [i for i in range(charas)]

    # 要求所有字出现次数不大于1并枚举所有词
    for word in enum_words(charas, len(charas),
                           max_counts=dict.fromkeys(charas, 1)):
        yield word


def detect_period(array: list, min_sampnum=None):
    """给出一个列表可能的预循环长度和周期"""

    if min_sampnum is None:
        min_sampnum = max(6, len(array) // 3)

    ultper = None

    for per in range(1, len(array) // 2):

        # 倒序尝试是否有周期为t的循环
        periodic = True
        for i in range(1, per + 1):
            if array[-i] != array[-i - per]:
                periodic = False
                break

        # 倒序尝试是否有周期为t的反循环
        flip = None
        if not periodic and type(array[0]) is int:

            # 多种不同的方式定义翻转
            for flip in [lambda n: n ^ 1, lambda n: -n, lambda n: 1 - n]:
                antiperiodic = True
                for i in range(1, per + 1):
                    if array[-i] != flip(array[-i - per]):
                        antiperiodic = False
                        break

                if antiperiodic:
                    break
        else:
            antiperiodic = False

        if periodic or antiperiodic:

            # 计算预循环长度
            preper = len(array) - per
            '''预循环长度'''
            for i in range(1, len(array) - per + 1):
                if preper == 0:
                    break
                elif array[-i] == (flip(array[-i - per]) if antiperiodic else array[-i - per]):
                    preper -= 1
                else:
                    break

            # 样本数足够大则有效
            sampnum = len(array) - preper - per
            if sampnum >= min_sampnum:
                ultper = (preper, per if periodic else 2 * per)
                break

    return ultper


"""图像绘制"""


def draw_text(image, pos, color: tuple = (128, 128, 128), text: str = None, size=20, anchor="mm"):
    """绘制文本"""

    font = ImageFont.truetype("simhei.ttf", size)
    draw = ImageDraw.Draw(image)
    draw.text(pos, text, fill=color, font=font, anchor=anchor)


def draw_arrow(image, pos, color: tuple = (128, 128, 128), line_width: int = 2,
               arrow_width: int = 8, tag: str = None, tag_size=20):
    """绘制箭头"""

    begin_r, end_r = 0, 0
    if len(pos) == 5:
        begin_r, end_r = pos[4], pos[4]
    elif len(pos) > 5:
        begin_r, end_r = pos[4], pos[5]

    begin_x, begin_y, end_x, end_y = pos[:4]

    # 宽度与高度（带符号）
    a, b = end_x - begin_x, end_y - begin_y

    # 长度
    c = math.sqrt(a ** 2 + b ** 2)

    # 预留空间
    if begin_r > 0:
        begin_x += begin_r * a / c
        begin_y += begin_r * b / c
    if end_r > 0:
        end_x -= end_r * a / c
        end_y -= end_r * b / c

    draw = ImageDraw.Draw(image)

    # 绘制直线
    draw.line((begin_x, begin_y, end_x, end_y), color, line_width)

    arrow1_x = end_x + (arrow_width * b / c) - (arrow_width * a / c)
    arrow1_y = end_y - (arrow_width * a / c) - (arrow_width * b / c)

    arrow2_x = end_x - (arrow_width * b / c) - (arrow_width * a / c)
    arrow2_y = end_y + (arrow_width * a / c) - (arrow_width * b / c)

    draw.line((end_x, end_y, arrow1_x, arrow1_y), color, line_width)
    draw.line((end_x, end_y, arrow2_x, arrow2_y), color, line_width)

    if tag is not None:
        # 文字偏离中点
        delta_tag_x = b / c - a / c
        delta_tag_y = -a / c - b / c

        anchor_x = "l" if delta_tag_x > 0 else "r"
        anchor_y = "a" if delta_tag_y > 0 else "d"
        anchor = anchor_x + anchor_y

        tag_x = begin_x + a / 2
        tag_y = begin_y + b / 2

        font = ImageFont.truetype("simhei.ttf", tag_size)
        draw.text((tag_x, tag_y), tag, fill=color, font=font, anchor=anchor)

