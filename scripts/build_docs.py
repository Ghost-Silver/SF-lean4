#!/usr/bin/env python3
"""
build_docs.py: 将 SFLean4 (LF, PLF, VFA) 的 57 个 .lean 源代码全自动转换为
极度精美、高可读性的 VitePress 文档网站源文件。

功能：
1. 提取 /-! ... -/ 作为 Markdown 教学散文排版；
2. 规范化并美化所有练习题标题（星级 Badge、难度分类、代码高亮）；
3. 将 Lean 4 形式化代码块包装为语法高亮块 ```lean ... ```；
4. 自动生成每卷的总览页 index.md 与完整章节树。
"""

import os
import re
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
SRC_DIR = REPO_ROOT / "SFLean4"
DOCS_DIR = REPO_ROOT / "docs"

VOLUMES = [
    {
        "id": "LF",
        "title": "卷一：逻辑基础 (Logical Foundations)",
        "subtitle": "形式化验证基石 · 现代函数式逻辑与证明自动化",
        "desc": "函数式编程、构造性逻辑、证明对象、柯里-霍华德同构与基础自动化证明技术",
        "dir": SRC_DIR / "LF",
        "out": DOCS_DIR / "LF",
        "chapters": [
            ("Basics", "基础篇：函数式编程与基础证明策略"),
            ("Induction", "归纳证明：数学归纳法与数制规范化"),
            ("Lists", "结构化数据：列表、数据对与多态偏映射"),
            ("Poly", "多态与高阶函数：全称多态与 Church 数"),
            ("Tactics", "策略进阶：反演、代换与泛化归纳"),
            ("Logic", "形式逻辑：构造性命题与逻辑联结词"),
            ("IndProp", "归纳命题与关系：置换、泵引理与正则导数"),
            ("Maps", "函数映射模型：全映射与偏映射词典"),
            ("ProofObjects", "柯里-霍华德同构：证明即程序，命题即类型"),
            ("IndPrinciples", "归纳法则深入：原理推导与自定义模式"),
            ("Rel", "二元关系：性质、自反传递闭包与全序"),
            ("Imp", "Imp 命令式语言：抽象语法与大步操作语义"),
            ("ImpParser", "词法分析与语法分析器"),
            ("ImpCEvalFun", "求值函数：步数索引与大步语义等价性"),
            ("Extraction", "代码抽取与编译执行"),
            ("Auto", "自动化证明策略：深度优先证明搜索与决策过程"),
            ("AltAuto", "自动化精粹：组合子与目标模式匹配"),
            ("Postscript", "全卷后记：理论回顾与进阶视野"),
            ("Bib", "参考文献与经典引文数据库"),
        ]
    },
    {
        "id": "PLF",
        "title": "卷二：编程语言基础 (Programming Language Foundations)",
        "subtitle": "程序语言理论 · 语义学、霍尔逻辑与类型安全",
        "desc": "程序等价性、霍尔逻辑、验证条件生成器 VCGen、小步操作语义与类型系统理论",
        "dir": SRC_DIR / "PLF",
        "out": DOCS_DIR / "PLF",
        "chapters": [
            ("Preface", "前言：课程指引与 PLF 路线图"),
            ("Maps", "映射库桥接"),
            ("Imp", "Imp 语言桥接"),
            ("Equiv", "程序等价性：行为等价、同余性与常量折叠"),
            ("Hoare", "霍尔逻辑 (I)：三元组、赋值规则与前向后向推理"),
            ("Hoare2", "霍尔逻辑 (II)：带标注程序与验证条件生成器 VCGen"),
            ("HoareAsLogic", "作为推导系统的霍尔逻辑：可靠性与相对完备性"),
            ("Smallstep", "小步操作语义：上下文归约、确定性与多步闭包"),
            ("Types", "类型系统入门：非类型化算术、简单类型与健全性"),
            ("Stlc", "简单类型 Lambda 演算 (STLC)：语法、替换与求值"),
            ("StlcProp", "STLC 性质验证：规范形式、弱化引理与保型性"),
            ("MoreStlc", "STLC 扩充：自然数、Let、积、和与递归定点"),
            ("Sub", "子类型化：前序关系、包容法则与函数逆变"),
            ("Typechecking", "类型检查器：可判定性算法与单子式实现"),
            ("Records", "记录类型系统：字段投影与类型安全"),
            ("References", "可变状态与内存引用：存储堆模型与定型保持"),
            ("RecordSub", "记录子类型化：宽度、深度与置换规则"),
            ("Norm", "STLC 强规范化：Tait 逻辑关系与停机性证明"),
            ("PE", "偏评估与在线特化：符号执行与流程图特化"),
            ("Postscript", "全卷后记：理论全景与工业验证前沿"),
            ("Bib", "参考文献数据库"),
        ]
    },
    {
        "id": "VFA",
        "title": "卷三：函数式算法验证 (Verified Functional Algorithms)",
        "subtitle": "经典数据结构与算法 · 正确性形式化全规约",
        "desc": "算法正确性证明、多重集表示不变量、Okasaki 红黑树、二进制前缀树与二项堆",
        "dir": SRC_DIR / "VFA",
        "out": DOCS_DIR / "VFA",
        "chapters": [
            ("Preface", "全书前言：算法形式化验证路线图"),
            ("Perm", "数值比较与置换技术基础：omega 决策过程与布尔反射"),
            ("Sort", "插入排序及其形式化规约：有序性与置换保持"),
            ("Multiset", "多重集抽象模型：内容计数函数与排序全规约"),
            ("BagPerm", "基于包的多重集置换：bag_eqv 与 Permutation 等价性"),
            ("Selection", "选择排序：燃油技术、度量良基递归与全序证明"),
            ("Merge", "归并排序：双步列表归纳与对数分治算法验证"),
            ("Maps", "全映射与偏映射：高阶函数模型与状态机基础"),
            ("SearchTree", "二叉搜索树 BST：表示不变量与抽象仿真模型"),
            ("ADT", "抽象数据类型规范：队列 ADT 与依值向量 vector"),
            ("Extract", "机器整数公理化：int 抽象与抽取版算法"),
            ("Redblack", "Okasaki 红黑树：平衡旋转、黑高度与对数平衡界限"),
            ("Trie", "二进制前缀树：positive 算术、对数时间查找表与双射"),
            ("Priqueue", "优先队列 ADT：PRIQUEUE 模块规范与参考实现"),
            ("Binom", "二项堆：可合并优先队列、进位链与多重集保持"),
            ("Decide", "判定过程编程：反射 reflect vs 构造性析取 sumbool"),
            ("Color", "图着色与寄存器分配：Kempe-Chaitin 算法与干扰图验证"),
        ]
    }
]

def format_exercise_heading(line: str) -> str:
    """
    将多样化的练习题标题统一转换为带 Badge 的美观标题
    """
    m = re.match(r'^#{3,4}\s*(?:[⭐️★]+\s*)?练习(?:题)?[:：]\s*(.*)$', line)
    if not m:
        return line
    rest = m.group(1).strip()
    
    # 模式 1: 3 星, standard (try_sequence)
    m1 = re.match(r'(\d+)\s*星\s*,\s*([^(]+)\(([^)]+)\)', rest)
    if m1:
        stars, tag, name = m1.group(1), m1.group(2).strip(), m1.group(3).strip()
        badge_text = f'{stars} 星 · {tag}'
        stars_num = int(stars)
        b_type = 'tip' if stars_num == 1 else ('info' if stars_num == 2 else ('warning' if stars_num == 3 else 'danger'))
        return f'### 🎯 练习：`{name}` <Badge type="{b_type}" text="{badge_text}" />'

    # 模式 2: nandb (1 星，标准) 或 InA_map_fst_key (2 星)
    m2 = re.match(r'([^(（]+)[(（]([^)）]+)[)）]', rest)
    if m2:
        name, info = m2.group(1).strip(), m2.group(2).strip()
        sm = re.search(r'(\d+)\s*星', info)
        stars_num = int(sm.group(1)) if sm else 1
        b_type = 'tip' if stars_num == 1 else ('info' if stars_num == 2 else ('warning' if stars_num == 3 else 'danger'))
        return f'### 🎯 练习：`{name}` <Badge type="{b_type}" text="{info}" />'

    return f'### 🎯 练习：{rest}'

def is_divider_line(line: str) -> bool:
    s = line.strip()
    return bool(re.match(r'^(?:/[-*]\s*[-=#*]{5,}\s*[-*]/|--\s*[-=#*]{5,})$', s))

def clean_code_block(code_str: str):
    lines = code_str.split('\n')
    cleaned_lines = []
    banner_headings = []
    
    for l in lines:
        s = l.strip()
        if is_divider_line(s):
            continue
        # 识别类似 -- * 战术组合子 (Tacticals) 的章节标题
        m_h1 = re.match(r'^--\s*[*#]{1}\s+(.*)$', s)
        m_h2 = re.match(r'^--\s*[*#]{2}\s+(.*)$', s)
        if m_h2:
            banner_headings.append(f"### {m_h2.group(1).strip()}")
            continue
        elif m_h1:
            banner_headings.append(f"## {m_h1.group(1).strip()}")
            continue
        cleaned_lines.append(l)
        
    code_body = '\n'.join(cleaned_lines).strip()
    return banner_headings, code_body

def convert_lean_to_markdown(lean_content: str, chapter_title: str) -> str:
    """
    智能解析 .lean 文件：
    将 /-! ... -/ 块作为一级 Markdown 正文；
    规范化练习题标题；
    过滤纯分隔符注释块（如 /- === -/），并将 -- * 标题提升为正规 Markdown 标题；
    将代码段落包裹在 ```lean ... ``` 中。
    """
    output = []
    
    idx = 0
    length = len(lean_content)
    current_code = []
    
    def flush_code():
        nonlocal current_code
        if current_code:
            code_str = "".join(current_code).strip()
            if code_str:
                banner_headings, code_body = clean_code_block(code_str)
                for h in banner_headings:
                    output.append(f"\n{h}\n")
                if code_body:
                    output.append(f"\n```lean\n{code_body}\n```\n")
            current_code = []
            
    while idx < length:
        if lean_content[idx:idx+4] == "/-!\n" or lean_content[idx:idx+4] == "/-! ":
            flush_code()
            end_idx = lean_content.find("-/", idx + 3)
            if end_idx == -1:
                end_idx = length
            doc_body = lean_content[idx+3:end_idx].strip()
            
            # 处理每行
            lines = doc_body.split("\n")
            processed_lines = []
            for line in lines:
                stripped = line.strip()
                if '练习' in stripped and (stripped.startswith('###') or stripped.startswith('####')):
                    processed_lines.append(format_exercise_heading(stripped))
                else:
                    processed_lines.append(line)
            
            joined_lines = "\n".join(processed_lines)
            output.append(f"\n{joined_lines}\n")
            idx = end_idx + 2
        else:
            current_code.append(lean_content[idx])
            idx += 1
            
    flush_code()
    return "".join(output).strip() + "\n"

def generate_volume_index(vol: dict):
    """
    为每个分卷生成专属的 index.md 总览页面
    """
    content = [
        "---",
        f"title: \"{vol['title']}\"",
        f"description: \"{vol['desc']}\"",
        "---",
        "",
        f"# {vol['title']}",
        "",
        f"> **{vol['subtitle']}**  ",
        f"> {vol['desc']}",
        "",
        "## 📚 本卷章节全景导读",
        "",
        "| 章节 | 名称与核心知识要点 | 快速直达 |",
        "| :--- | :--- | :--- |"
    ]
    
    for i, (name, desc) in enumerate(vol["chapters"], 1):
        content.append(f"| **第 {i} 章** | **{name}** · {desc} | [阅读章节 →](./{name}) |")
        
    first_ch = vol["chapters"][0][0]
    content.extend([
        "",
        "---",
        "",
        f"👉 [从第一章 **{first_ch}** 开始阅读 →](./{first_ch})",
        ""
    ])
    
    index_path = vol["out"] / "index.md"
    index_path.write_text("\n".join(content), encoding="utf-8")
    print(f"  ✓ 已生成卷首页 {vol['id']}/index.md")

def main():
    print("🚀 开始全量生成《软件基础》Lean 4 静态网站内容...")
    
    for vol in VOLUMES:
        vol["out"].mkdir(parents=True, exist_ok=True)
        print(f"\n📚 处理 {vol['title']}...")
        
        generate_volume_index(vol)
        
        for name, desc in vol["chapters"]:
            lean_path = vol["dir"] / f"{name}.lean"
            md_path = vol["out"] / f"{name}.md"
            
            if not lean_path.exists():
                print(f"⚠️  警告：未找到 {lean_path}")
                continue
                
            content = lean_path.read_text(encoding="utf-8")
            md_content = convert_lean_to_markdown(content, f"{name}: {desc}")
            
            # 顶部加上章节元数据
            header = f"---\ntitle: \"{name}: {desc}\"\n---\n\n"
            md_path.write_text(header + md_content, encoding="utf-8")
            print(f"  ✓ 已生成 {vol['id']}/{name}.md")
            
    print("\n🎉 57 个章节文档及各卷首页已全量转换完成！")

if __name__ == "__main__":
    main()
