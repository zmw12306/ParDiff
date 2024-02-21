#!/usr/bin/python3

import struct
import sys


class Node:
    def __init__(self, data):
        self.data = data
        self.next_node = None


class SLinkedList:
    def __init__(self):
        self.head_node = None

    def replace(self, prev, node, n1, n2):
        if prev is not None:
            prev.next_node = n1
        else:
            assert node == self.head_node
            self.head_node = n1
        n2.next_node = node.next_node

    def split(self, i, j):
        prev_node = None
        node = self.head_node
        i = i * 2
        j = (j + 1) * 2 - 1

        while node is not None:
            if i >= 0 and j < len(node.data):
                if i == 0 and j + 1 == len(node.data):
                    return
                elif i == 0:
                    # split and ret
                    n1 = Node(node.data[i:j + 1])
                    n2 = Node(node.data[j + 1:])
                    n1.next_node = n2
                    self.replace(prev_node, node, n1, n2)
                    return
                elif j + 1 == len(node.data):
                    # split and ret
                    assert i > 0
                    n1 = Node(node.data[0:i])
                    n2 = Node(node.data[i:])
                    n1.next_node = n2
                    self.replace(prev_node, node, n1, n2)
                    return
                else:
                    n1 = Node(node.data[0:i])
                    n2 = Node(node.data[i:j + 1])
                    n3 = Node(node.data[j + 1:])
                    n1.next_node = n2
                    n2.next_node = n3
                    self.replace(prev_node, node, n1, n3)
                    return
            elif i < 0:
                return
            elif i < len(node.data) <= j:
                return

            i = i - len(node.data)
            j = j - len(node.data)
            prev_node = node
            node = node.next_node

    def print(self):
        ret = ""
        node = self.head_node
        while node is not None:
            ret = ret + "[%s]" % node.data
            node = node.next_node
        print(ret)
        return ret


def read_aflog(filename):
    logs = []
    with open(filename, "r") as logfile:
        line = logfile.readline()
        log = []
        while line:
            line = line.strip()
            if line.startswith("[autoformat]"):
                line = line[len("[autoformat]"):].strip()
                rets = line.split(',')
                id = int(rets[0])
                callstack = "->".join(rets[1:])
                log.append((id, callstack))
            elif line.startswith("---"):
                logs.append(log)
                log = []
            line = logfile.readline()
    return logs


def read_packets(filename):
    f = open(filename, 'rb')
    fcontent = f.read()
    f.close()
    i = 0
    records = []
    total_len = 0
    while i < len(fcontent):
        rec_len = struct.unpack("i", fcontent[i: i + 4])[0]
        record = fcontent[i + 4: i + 4 + rec_len]
        i += 4 + rec_len
        records.append((rec_len, record))
        total_len += rec_len + 16
    return records


def segment(log, packet, file):
    packet_str = ''.join(format(x, '02x') for x in packet[1])
    packet_len = packet[0]
    assert packet_len * 2 == len(packet_str)
    print(packet_str)
    print(log)

    seg_list = SLinkedList()
    seg_list.head_node = Node(packet_str)

    i = 0
    while i < len(log):
        curr = log[i]
        j = i + 1
        while j < len(log):
            next = log[j]
            if curr[0] + 1 == next[0] and curr[1] == next[1]:
                j = j + 1
                curr = next
            else:
                break
        # field: [log[i][0], log[j - 1][0]]
        print("split %d, %d" % (log[i][0], log[j - 1][0]))
        seg_list.split(log[i][0], log[j - 1][0])
        i = j

    ret = seg_list.print()
    file.write(ret + "\n")


if __name__ == '__main__':
    if len(sys.argv) != 4:
        print("usage: ./autoformat.py [AFLOG_FILENAME] [BIN_FILENAME] [OUTPUT]")

    logs = read_aflog(sys.argv[1])
    packets = read_packets(sys.argv[2])
    print("log length: %d" % len(logs))
    print("packet length: %d" % len(packets))
    assert len(logs) == len(packets)

    output = open(sys.argv[3], "w+")
    for i in range(len(logs)):
        segment(logs[i], packets[i], output)
    output.close()
