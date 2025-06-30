# 形式化方法 实验小作业4（作业3） Frama-c

## 1. 代码

使用了一段冒泡排序的代码

```c
#include <stdio.h>

void bubbleSort(int arr[], int n) {
    int i, j, temp;
    for (i = 0; i < n-1; i++) {
        for (j = 0; j < n-i-1; j++) {
            if (arr[j] > arr[j+1]) {
                // 交换元素
                temp = arr[j];
                arr[j] = arr[j+1];
                arr[j+1] = temp;
            }
        }
    }
}

// 打印数组的函数
void printArray(int arr[], int n) {
    int i;
    for (i = 0; i < n; i++) {
        printf("%d ", arr[i]);
    }
    printf("\n");
}

int main() {
    int arr[] = {64, 34, 25, 12, 22, 11, 90};
    int n = sizeof(arr)/sizeof(arr[0]);
    
    printf("排序前的数组: ");
    printArray(arr, n);
    
    bubbleSort(arr, n);
    
    printf("排序后的数组: ");
    printArray(arr, n);
    
    return 0;
}

```

## 2.运行结果

通过分析可以清楚的知道每个值的范围和情况，且得出的报告显示该程序是有效且无漏洞的

<img src="C:\Users\yyc\AppData\Roaming\Typora\typora-user-images\image-20250516134029816.png" alt="image-20250516134029816" style="zoom:50%;" />![image-20250516134050793](C:\Users\yyc\AppData\Roaming\Typora\typora-user-images\image-20250516134050793.png)

<img src="C:\Users\yyc\AppData\Roaming\Typora\typora-user-images\image-20250516134050793.png" alt="image-20250516134050793" style="zoom:50%;" />

## 3.其他

安装`frama-c`参照了[Get Frama-C](https://frama-c.com/html/get-frama-c.html)的教程，环境为WSL-Ubuntu22.04

