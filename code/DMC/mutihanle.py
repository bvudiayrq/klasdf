import os
import concurrent.futures
from concurrent.futures import as_completed
import pickle
import glob
import signal
import logging
import psutil
import time
import resource
import subprocess
import gc
import re

# 配置logging模块
logging.basicConfig(filename='mutihanle.log', level=logging.INFO, format='%(asctime)s - %(message)s')

output_files = []
stop_new_tasks = False
THREAD_LIMIT = 64

# 设置进程的内存限制为40G
resource.setrlimit(resource.RLIMIT_AS, (45 * 1024 ** 3, resource.RLIM_INFINITY))

# 获取系统的内存信息
def get_available_memory():
    mem_info = psutil.virtual_memory()
    # 计算可以使用的内存（剩余内存 - 8G）
    available_memory = mem_info.available - 8 * 1024 ** 3
    return available_memory


# 创建线程池
# executor = concurrent.futures.ThreadPoolExecutor(max_workers=33)

# 提交任务
def submit_task(executor,task, *args):
    while True:
        if get_available_memory() > 0:
            return executor.submit(task, *args)  # return the Future object
        else:
            time.sleep(40)  # 等待40秒再检查


# with open('ERC20_hash.pickle', 'rb') as file:
#     data = pickle.load(file)

# # 打印前三个元素
# for item in data[:3]:
#     print(item)
# print(len(data))
# print("......")

# 检查是否只存在constructor函数
def check_constructor_only(filename):
    with open(filename, 'r') as f:
        lines = f.readlines()
        for line in lines:
            only_constructor = True
            if 'Func_name' in line and 'func_type' in line:
                match = re.search(r'Func_name:\s*(.*?)\s+func_type:\s*(.*?)$', line)
                if match:
                    func_name = match.group(1)
                    if func_name not in ["constructor","fallback"]:
                        only_constructor = False
                        break
    if not only_constructor:
        return False
    open(filename, 'w').close()
    return True

# 检查是否有approve等函数是FunctionType.UNKNOWN
def check_unknown_function_type(filename):
    check_function_list = ["approve(address,uint256)","transfer(address,uint256)","transferFrom(address,address,uint256)","approveAndCall(address,uint256,bytes)","setApprovalForAll(address,bool)"]
    with open(filename, 'r') as f:
        lines = f.readlines()
        for line in lines:
            if 'Func_name' in line and 'func_type' in line:
                match = re.search(r'Func_name:\s*(.*?)\s+func_type:\s*(.*?)$', line)
                if match:
                    func_name = match.group(1)
                    func_type = match.group(2)
                    if func_name in check_function_list and func_type == "FunctionType.UNKNOWN":
                        return True
    return False
    

# 在 run_myth 函数中，使用 subprocess 模块执行命令
def run_myth(type, address, creationCode, index):
    try:
        output_file = f'./output/{type}/{index}/{address}.txt'
        # 设置代理
        os.environ['http_proxy'] = "http://127.0.0.1:7890"
        os.environ['https_proxy'] = "http://127.0.0.1:7890"
        # 检查文件是否存在，如果存在则跳过
        if os.path.exists(output_file):
            # 检查是否只有constructor函数(和fallback函数)
            if not check_constructor_only(output_file):
                return
            open(output_file, 'w').close()
                
                                
        # 计时
        start_time = time.time()
        run_type = "type1:"
        command = ['python', '../mythril/myth', 'a', '-c', creationCode,
                   '--create-timeout', '30',
                   '--execution-timeout', '1800',
                   '--transaction-sequences', '[[0x095ea7b3,0xcae9ca51,0xa22cb465,0xa9059cbb],[0x23b872dd,0x42842e0e]]',
                   '--infura-id', 'a00f214ce0b940e2a5b67459c2b1fcc3',
                    '--solver-timeout', '13000'] #'--enable-state-merging'会产生更多更复杂的结构,--create-timeout
        with open(output_file, 'w') as f:
            f.write(f'Command: {" ".join(command)}\n')
            subprocess.run(command, stdout=f, stderr=subprocess.STDOUT)
        end_time = time.time()
        if check_constructor_only(output_file): # 运行时间小于13s，可能出现异常，例如创建合约事件不足
            start_time = time.time()
            # logging.error(f"{output_file} run time less than 13s")
            run_type = "type2:"
            command = ['python', '../mythril/myth', 'a', '-c', creationCode,
                    '--create-timeout', '60',
                    '--execution-timeout', '1800',
                    '--transaction-sequences', '[[0x095ea7b3,0xcae9ca51,0xa22cb465,0xa9059cbb],[0x23b872dd,0x42842e0e]]',
                    '--infura-id', 'a00f214ce0b940e2a5b67459c2b1fcc3',
                    '--solver-timeout', '13000']
            # 清空并重新运行
            with open(output_file, 'w') as f:
                f.write(f'new Command: {" ".join(command)}\n')
                subprocess.run(command, stdout=f, stderr=subprocess.STDOUT)
            end_time = time.time()
            if check_constructor_only(output_file): # 使用链上数据
                start_time = time.time()
                run_type = "type3:"
                command = ['python', '../mythril/myth', 'a', '-a', address,
                    '--create-timeout', '60',
                    '--execution-timeout', '1800',
                    '--transaction-sequences', '[[0x095ea7b3,0xcae9ca51,0xa22cb465,0xa9059cbb],[0x23b872dd,0x42842e0e]]',
                    '--infura-id', 'a00f214ce0b940e2a5b67459c2b1fcc3',
                    '--solver-timeout', '15000']
                # 清空并重新运行
                with open(output_file, 'w') as f:
                    f.write(f'new Command: {" ".join(command)}\n')
                    subprocess.run(command, stdout=f, stderr=subprocess.STDOUT)
                end_time = time.time()
        # 部分合约需要检测三笔交易
        if check_unknown_function_type(output_file):
            start_time = time.time()
            if run_type == "type1:":
                command = ['python', '../mythril/myth', 'a', '-c', creationCode,
                    '--create-timeout', '30',
                    '--execution-timeout', '5400',
                    '--transaction-sequences', '[[],[0x095ea7b3,0xcae9ca51,0xa22cb465,0xa9059cbb],[0x23b872dd,0x42842e0e]]',
                    '-t','3',
                    '--infura-id', 'a00f214ce0b940e2a5b67459c2b1fcc3',
                    '--solver-timeout', '15000']
            elif run_type == "type2:":
                command = ['python', '../mythril/myth', 'a', '-c', creationCode,
                    '--create-timeout', '60',
                    '--execution-timeout', '5400',
                    '--transaction-sequences', '[[],[0x095ea7b3,0xcae9ca51,0xa22cb465,0xa9059cbb],[0x23b872dd,0x42842e0e]]',
                    '-t','3',
                    '--infura-id', 'a00f214ce0b940e2a5b67459c2b1fcc3',
                    '--solver-timeout', '15000']
            else:
                command = ['python', '../mythril/myth', 'a', '-a', address,
                   '--create-timeout', '60',
                   '--execution-timeout', '5400',
                   '--transaction-sequences', '[[],[0x095ea7b3,0xcae9ca51,0xa22cb465,0xa9059cbb],[0x23b872dd,0x42842e0e]]',
                   '-t','3',
                   '--infura-id', 'a00f214ce0b940e2a5b67459c2b1fcc3',
                    '--solver-timeout', '15000']
            # 清空并重新运行
            with open(output_file, 'w') as f:
                f.write(f'new Command: {" ".join(command)}\n')
                subprocess.run(command, stdout=f, stderr=subprocess.STDOUT)
            end_time = time.time()
        
        # 输出到output_files末尾，计时并标记运行完成
        with open(output_file, 'a') as f:
            f.write(f'\n{run_type}Time taken: {end_time - start_time} seconds\n')
    except Exception as e:
        logging.error(f"Error running myth: {e} in {type} {address}")

    
def handle_sigint(sig, frame):
    global stop_new_tasks
    stop_new_tasks = True
    
signal.signal(signal.SIGTSTP, handle_sigint)

def split_list(lst, n):
    k, m = divmod(len(lst), n)
    return [lst[i*k + min(i, m):(i+1)*k + min(i+1, m)] for i in range(n)]

# Function to process a chunk of records
def process_chunk(chunk_file,type,index,executor):
    with open(chunk_file, 'rb') as f:
        chunk = pickle.load(f)
    if not os.path.exists(f'./output'):
        os.makedirs(f'./output')
        print(f'./output created')
    if not os.path.exists(f'./output/{type}'):
        os.makedirs(f'./output/{type}')
        print(f'./output/{type} created')
    if not os.path.exists(f'./output/{type}/{index}'):
        os.makedirs(f'./output/{type}/{index}')
        logging.info(f'./output/{type}/{index} created')

    futures = [submit_task(executor,run_myth, type, address, creationCode, index) for address, creationCode in chunk[:1000]]
    for future in as_completed(futures):
        future.result()
    
    # executor.shutdown()
    # 等待所有任务完成
    concurrent.futures.wait(futures)
    logging.info(f"{chunk_file} done")
    print(f"{chunk_file} done")

def load_creaionCode(file_path):
    with open(file_path, 'rb') as f:
        records = []
        
        data = pickle.load(f)
        print(f"load {file_path} data done")
        records = [(contract[1][0], contract[2]) for contract in data]
    return records

def dataset_process(erc_type, chunk_start, chunk_end):
    # 如果不存在目录则创建目录(存放拆分后的dataset0数据)
    if not os.path.exists('temp'):
        os.makedirs('temp')
    # 如果所有ERC20_chunk_{i}.pickle都存在，则不需要重新生成
    if len(glob.glob(f'temp/{erc_type}_chunk_*.pickle')) != 10:
        records = load_creaionCode(f'dataset/{erc_type}_contract.pkl')
        # Split records into 10 chunks
        chunks = split_list(records, 10)
        # Save each chunk to a separate file
        for i, chunk in enumerate(chunks):
            # with open(f'temp/ERC20_chunk_{i}.pickle', 'wb') as f:
            with open(f'temp/{erc_type}_chunk_{i}.pickle', 'wb') as f:
                pickle.dump(chunk, f)
        # print("save split data done")
        logging.info(f"save split data done")
        # Delete records and chunks to free up memory
        del records
        del chunks
    # Force garbage collection
    gc.collect()
    # Process each chunk sequentially
    # logging.info(f"start processing {erc_type} data")
    logging.info(f"{time.strftime('%Y-%m-%d %H:%M:%S', time.localtime())} start processing {erc_type} data")
    # shell启用代理
    #export http_proxy="http://127.0.0.1:7890"
    #export https_proxy="http://127.0.0.1:7890"
    os.environ['http_proxy'] = "http://127.0.0.1:7890"
    os.environ['https_proxy'] = "http://127.0.0.1:7890"
    
    
    # 创建线程池
    executor = concurrent.futures.ThreadPoolExecutor(max_workers=THREAD_LIMIT)
    for i in range(chunk_start, chunk_end):
        # process_chunk(f'temp/ERC20_chunk_{i}.pickle',"ERC20",i)
        process_chunk(f'temp/{erc_type}_chunk_{i}.pickle',erc_type,i,executor)
 
    # 等待所有任务执行完毕
    executor.shutdown()
    
# 统计结果,所有结果的平均用时，最小用时，最大用时，能使80%完成的用时
def time_statistics(erc_type):
    # 读取OUTPUT/erc_type文件夹下所有txt文件，统计用时
    time_list = [] # 统计用时
    # 统计
    run_success_count = 0
    run_failed_count = 0
    run_failed_files = []
    no_issues_count = 0
    issues_file_count = 0
    issues_file = []
    func_type_dict = {} # 检测的函数名、函数类型和数量
    constructor_count = 0 # 只有constructor函数的合约数量
    constructor_and_fallback_count = 0 # 只有constructor和fallback函数的合约数量
    # constructor_list = [] # 只有constructor(和fallback)函数的合约地址列表
    run_type_counts = {
        "type1": 0,
        "type2": 0,
        "type3": 0
    }
    # 错误信息字典
    vountability_counts = {}
    in_vulnerability_block = False # 表示是否在漏洞块中
    line_count = 0 # 用于定位漏洞位置
    
    for filename in glob.glob(f'./output/{erc_type}/0/*.txt'):
        with open(filename, 'r') as f:
            flag_run_success = False # 未正常运行完成
            flag_no_issues = False
            flag_func_dict = False
            only_constructor = True
            constructor_and_fallback = True        
            lines = f.readlines()
            for line in lines:
                if 'Time taken' in line:
                    #f.write(f'\n{run_type}Time taken: {end_time - start_time} seconds\n')
                    run_type = line.split(":")[0]
                    run_time = float(line.split(' ')[-2])
                    # if run_time < 5: #运行时间小于1秒大概率出现异常
                    #     logging.error(f"{filename} run time less than 5s")
                    # else:
                    if run_type in run_type_counts:
                        run_type_counts[run_type] += 1
                    time_list.append(run_time)
                    flag_run_success = True
                elif "Traceback (most recent call last):" in line:
                    flag_run_success = False
                    break
                elif 'The analysis was completed successfully. No issues were detected.' in line:
                    flag_no_issues = True
                if flag_func_dict and 'Func_name' in line and 'func_type' in line:
                    match = re.search(r'Func_name:\s*(.*?)\s+func_type:\s*(.*?)$', line)
                    if match:
                        func_name = match.group(1)
                        func_type = match.group(2)
                        if func_name != "constructor":
                            only_constructor = False
                            if func_name != "fallback":
                                constructor_and_fallback = False
                        if func_name in func_type_dict and func_type in func_type_dict[func_name]:
                            func_type_dict[func_name][func_type] += 1
                        elif func_name in func_type_dict:
                            func_type_dict[func_name][func_type] = 1
                        else:
                            func_type_dict[func_name] = {}
                            func_type_dict[func_name][func_type] = 1
                elif "function_dict:" in line:
                    flag_func_dict = True
            # 是否只有constructor函数
            if only_constructor:
                constructor_count += 1
            if not only_constructor and constructor_and_fallback:
                constructor_and_fallback_count += 1
                logging.info(f"{filename} include {func_name} {func_type}")
            # if only_constructor or constructor_and_fallback:
            #     constructor_list.append(filename)

            if not flag_run_success: # 有异常退出或者没有运行成功
                # logging.error(f"{filename} run failed")
                run_failed_count += 1
                run_failed_files.append(filename)
            else:
                run_success_count += 1
                # 没有漏洞
                if flag_no_issues:
                    # logging.info(f"{filename} no issues")
                    no_issues_count += 1
                else:
                    issues_file_count += 1
                    vulnerability_type =""
                    func_name = ""
                    for line in lines:
                        if "handle ====" in line:
                            in_vulnerability_block = True
                            line_count = 0 # 重置行数计数器
                        elif "--------------------" in line:
                            in_vulnerability_block = False
                        elif in_vulnerability_block:
                            line_count += 1
                            # print(f"{line_count} {line}")
                            if line_count == 4: #Function name: many_msg_babbage(bytes1) or transfer(address,uint256)
                                func_name = line.split(":")[1].strip()
                                # print(func_name)
                            elif line_count == 8:
                                # 提取漏洞类型
                                vulnerability_type = line.strip()
                                # 更新统计计数
                                if func_name in vountability_counts:
                                    if vulnerability_type in vountability_counts[func_name]:
                                        vountability_counts[func_name][vulnerability_type] += 1
                                        issues_file.append((filename,func_name,vulnerability_type))
                                    else:
                                        vountability_counts[func_name][vulnerability_type] = 1
                                        issues_file.append((filename,func_name,vulnerability_type))
                                else:
                                    vountability_counts[func_name] = {}
                                    vountability_counts[func_name][vulnerability_type] = 1
                                    issues_file.append((filename,func_name,vulnerability_type))
                          
    # 统计结果
    logging.info(f"=== {erc_type} time statistics ===")
    logging.info(f"{erc_type} total count: {len(time_list)}")
    if len(time_list) > 0:
        # 总用时，平均用时，最小用时，最大用时，80%用时
        total_time = sum(time_list)
        average_time = sum(time_list) / len(time_list)
        min_time = min(time_list)
        max_time = max(time_list)
        time_list.sort()
        eighty_percent_time = time_list[int(len(time_list) * 0.8)]
        # 除去运行时间小于90s的合约后，检测80%的合约用时
        time_list_more_90 = [time for time in time_list if time > 90]
        eighty_percent_time2 = time_list_more_90[int(len(time_list_more_90) * 0.8)]
        # 统计运行时间小于20s和1min的合约
        less_20s = len([time for time in time_list if time < 35])
        less_1min = len([time for time in time_list if time < 100])
        # 统计运行事件超过1800s的
        more_30min = len([time for time in time_list if time > 1800])
        logging.info(f"total time: {total_time}")
        logging.info(f"average time: {average_time}")
        logging.info(f"min time: {min_time}")
        logging.info(f" max time: {max_time}")
        logging.info(f"80% time: {eighty_percent_time}")
        logging.info(f"in runtime more than 90s, 80% time: {eighty_percent_time2}")
        logging.info(f"less 35s count: {less_20s}")
        logging.info(f"less 100s count: {less_1min}")
        logging.info(f"more 1800s count: {more_30min}")
        # run_type统计
        for run_type in run_type_counts:
            logging.info(f"{run_type} count: {run_type_counts[run_type]}")
    else:
        logging.info(f"{erc_type} no time data")
    logging.info(f"=== {erc_type} error statistics ===")
    logging.info(f"{erc_type} run success count: {len(time_list)}")
    logging.info(f"* {erc_type} no issues count: {no_issues_count}")
    logging.info(f"* {erc_type} issues count: {issues_file_count}")
    # logging.info(f"* {erc_type} issues file: \n{issues_file}")
    logging.info(f"{erc_type} run failed count: {run_failed_count}")
    for failed_file in run_failed_files:
        logging.info(f"{failed_file} run failed")
    ## 函数检测情况
    logging.info("=== function type check statistics ===")
    logging.info(f"only constructor count: {constructor_count}")
    logging.info(f"constructor and fallback count: {constructor_and_fallback_count}")
    check_function_list = ["approve(address,uint256)","transfer(address,uint256)","transferFrom(address,address,uint256)","approveAndCall(address,uint256,bytes)","setApprovalForAll(address,bool)"]
    for func_name in func_type_dict:
        # 如果func_name字符串中不包含approve等关键函数，则跳过
        if not any([check_func in func_name for check_func in check_function_list]):
            continue
        for func_type in func_type_dict[func_name]:
            logging.info(f"{func_name}->{func_type}: {func_type_dict[func_name][func_type]}")
    logging.info("=== vulnerability statistics ===")
    # print(vountability_counts)
    for func_name in vountability_counts:
        for vulnerability_type in vountability_counts[func_name]:
            logging.info(f"{func_name}->{vulnerability_type}: {vountability_counts[func_name][vulnerability_type]}")
    logging.info("=== issues files ===")
    # for filename in issues_file:
    for (filename,func_name,vulnerability_type) in issues_file:
        logging.info(f"{filename} include :{func_name} {vulnerability_type}")
    
    

def main():
    # 输入检测类型ERC20/ERC721
    erc_type = input("请输入检测类型ERC:(20/721) ")
    if erc_type not in ["20","721"]:
        print("输入有误")
        return
    erc_type = f"ERC{erc_type}"
    # 读取并分割文件
    # 输入chunk_start,chunk_end，并检查是否满足0<=chunk_start<chunk_end<=10
    chunk_start = int(input("Please input the start of the chunk range: "))
    chunk_end = int(input("Please input the end of the chunk range: "))
    if 0 <= chunk_start < chunk_end <= 10:
        # 等待5s后开始
        time.sleep(5)
        print(f"=== Start processing {erc_type} data. ===")
        dataset_process(erc_type, chunk_start, chunk_end) # 处理ERC数据
        time_statistics(erc_type) # 统计结果
    elif chunk_start == chunk_end:
        time_statistics(erc_type)
    else:
        print("Invalid range. Please ensure 0 <= chunk_start < chunk_end <= 10.")

if __name__ == '__main__':
    main()

