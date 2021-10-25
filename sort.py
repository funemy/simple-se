def insertion_sort(arr, l):
    for i in range(1, l):
        tmp = arr[i]
        k = i-1
        for j in range(i-1, -1, -1):
            if tmp < arr[j]:
                arr[j+1] = arr[j]
                k = k - 1
        arr[k+1] = tmp
    return arr
            

if __name__ == "__main__":
    # arr = [8,3,21,10,76,12,2,4,6,9,11,22,78,99,21]
    arr = [8,3,21,10]
    l = len(arr)
    res = insertion_sort(arr, l)
    print(res)